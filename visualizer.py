#!/usr/bin/env python
#
# Determine which tables are being referenced in a query
#

import argparse
import configparser
import enum
import hashlib
import pathlib
import tempfile
from typing import Self
import webbrowser
import sqlglot


class NodeType(enum.Enum):
    CTE = 0
    Table = 1
    Select = 2


class DAGNode:
    
    def __init__(self, fqn: str, node_t: NodeType):
        self.name = fqn
        self.node_t = node_t
        self.sources = list()
        self.slen = 0
        self.id = None
        self.color = None

    def __iter__(self):
        for source in self.sources:
            yield source

            for sub in source:
                yield sub

    def add_source(self, source: Self):
        self.sources.append(source)
        self.slen += 1

    def swap_source(self, idx: int, source: Self):
        self.sources[idx] = source

    def sort(self, key=None):
        self.sources.sort(key=key)

    def pairs(self):
        for source in self.sources:
            yield (source, self)


class SimplifiedDAG:

    def __init__(self):
        self.trees = list()
        self.next_id = 0
        self.colors = {
            "srcNode": "fill:#EEEEEE,stroke:#666666",
            "cteNode": "fill:#7D858D,stroke:#666666",
            "intNode": "fill:#AACCD7,stroke:#666666",
            "endNode": "fill:#FDE1A7,stroke:#666666"}

    def add_class_style(self, colors: dict[str, str]):
        """
        Add a new color rule to the mermaid diagram. Must follow the mermaid
        classDef spec: {'class_name': 'fill:#HEXHEX[,etc];'}
        """
        self.colors.update(colors)

    def set_node_color_rule(self, callback):
        """
        Assign the color rule for all nodes using a color rule callable.
        """
        for branch in self.trees:
            branch.color = callback(branch)

    def sort(self, key=None):
        """
        Sort the DAG using an optionally provided callable. Sorting is used
        to reorder nodes in the trees, which can impact how they are rendered
        by mermaid. This is helpful for keeping certain nodes grouped, but is
        not always guaranteed.
        """
        self.trees.sort(key=key)

        for branch in self.trees:
            branch.sort(key=key)

    def iter_deep(self):
        """
        Iterate over the DAG's trees, descending each branch until exhaustion.
        """
        for branch in self.trees:
            yield branch

            for node in branch:
                yield node

    def assign_id(self, node: DAGNode):
        """
        Assign an ID to a node in the DAG. This ID is used by the mermaid
        rendering step.
        """
        node.id = self.next_id
        self.next_id += 1

    def add_node(self, node: DAGNode):
        """
        Add a node to the DAG's root node list.
        """
        self.assign_id(node)
        self.trees.append(node)

    def rem_node(self, node: DAGNode):
        """
        Remove a given node from the DAG's root node list.
        """
        self.trees.remove(node)

    def root_nodes(self):
        """
        Returns root nodes of the DAG: those without any sources.
        """
        seen = set()

        for src in self.iter_deep():
            if src.slen == 0 and src.name not in seen:
                seen.add(src.name)
                yield src

    def end_nodes(self):
        """
        Returns leaf nodes of the DAG: those which are not sources of
        any other nodes.
        """
        return self.trees

    def unq_nodes(self):
        """
        Returns the unique nodes in the DAG, while retaining sorting
        slightly better than `set`.
        """
        seen = list()

        for node in self.iter_deep():
            if node.name not in seen:
                seen.append(node)

        return seen

    def insert(self, parent: DAGNode) -> None:
        """
        Insert a node into the DAG. Associate any previously known sources
        with this node's sources, invalidating previously generated nodes.
        """
        for i, child in enumerate(parent.sources):
            known = None
            for branch in self.iter_deep():
                if child.name == branch.name and branch.node_t != NodeType.CTE:
                    known = branch
                    break

            if known is not None:
                if known in self.trees:
                    self.rem_node(known)

                parent.swap_source(i, known)

            else:
                self.assign_id(child)

        self.add_node(parent)

    def mm(self) -> str:
        """
        Generate a flowchart mermaid graph diagram from the DAG.
        """
        mmc = "\ngraph LR\n"

        node_class = {
            "srcNode": [],
            "cteNode": [],
            "intNode": [],
            "endNode": []}

        root_nodes = list(self.root_nodes())
        end_nodes = list(self.end_nodes())

        # Any given node can reference a node that has already been seen, so
        # this needs to be deduplicated. Probably a better way to do this
        unq_nodes = self.unq_nodes()

        for branch in unq_nodes:
            mmc += f"""\t{branch.id}["{branch.name}"]\n"""

            if branch.color:
                if branch.color not in node_class:
                    node_class[branch.color] = []

                node_class[branch.color].append(branch.id)

            elif branch.node_t == NodeType.CTE:
                node_class['cteNode'].append(branch.id)

            elif branch in root_nodes:
                node_class['srcNode'].append(branch.id)

            elif branch in end_nodes:
                node_class['endNode'].append(branch.id)

            else:
                node_class['intNode'].append(branch.id)

            for src, tgt in branch.pairs():
                mmc += f"""\t{src.id} --> {tgt.id}\n"""

        for class_nm in node_class.keys():
            class_def = self.colors.get(class_nm)
            if class_def:
                mmc += f"\n\tclassDef {class_nm} {class_def};"
        
        for class_nm, nodes in node_class.items():
            if nodes:
                mmc += f"\n\tclass {','.join(str(x) for x in nodes)} {class_nm}"

        mmc += "\n"

        return mmc


def read_parse(path: pathlib.Path, dialect=None) -> list:
    """
    Read and parse a sql file or a directory of sql files, returning a list
    of ASTs.
    """
    if path.is_dir():
        # TODO:
        # Here we need to "discover" if the directory is a dbt project and
        # handle the rendering of dbt models. Currently, sqlglot cannot parse
        # dbt models with {{ ref }} or {{ source }} statements.
        files = path.glob('**/*.sql')
    else:
        files = [path]

    asts = []
    for file in files:
        with open(file, 'r') as f:
            # NOTE:
            # If reading a directory of files, this places every query in the
            # same environment. In the future, consider whether scoping these
            # environments is helpful or worth placing behind a flag.
            #
            # For example, if discovered to be in a dbt project, place models
            # in the same lexical scope by default. Otherwise, if just a
            # collection of scripts, separate queries into their own envs, and
            # look to the caller to override this behavior using a cli flag.
            asts.extend(sqlglot.parse(f.read(), dialect=dialect))

    return asts

def is_create(ast: sqlglot.exp.Expression) -> bool:
    return type(ast) == sqlglot.exp.Create

def is_select(ast: sqlglot.exp.Expression) -> bool:
    return type(ast) == sqlglot.exp.Select \
        or type(ast) == sqlglot.exp.Subquery \
        or type(ast) == sqlglot.exp.Union \
        or type(ast) == sqlglot.exp.Intersect \
        or type(ast) == sqlglot.exp.Except

def find_statement(ast: sqlglot.exp.Expression) -> DAGNode:
    if is_create(ast):
        return DAGNode(ast.this.name.upper(), NodeType.Table)
    else:
        return DAGNode("Select#" + short_hash(ast), NodeType.Select)

def find_tables(ast: sqlglot.exp.Expression, incl_subquery: bool) -> set:
    tables = set()

    # Probably a better way to descend this tree
    expr = ast.expression if is_create(ast) else ast

    if is_select(expr):
        ctes = {x.alias.upper() for x in expr.find_all(sqlglot.exp.CTE)}

        for table in expr.find_all(sqlglot.exp.Table):
            fqn = '.'.join(x.name.upper() for x in table.parts)

            if fqn not in ctes:
                node = DAGNode(fqn, NodeType.Table)
                tables.add(node)

    return tables

def process_ast(ast: sqlglot.exp.Expression, incl_subquery: bool) -> DAGNode:
    if is_create(ast) or is_select(ast):
        node = find_statement(ast)

        for source in find_tables(ast, incl_subquery):
            node.add_source(source)

        # DEBUG
        node.ast = ast

        return node

def default_color_rule(node: DAGNode):
    """
    Defines the default color rule for nodes styles.
    """
    path = node.name.split('.')
    return path[0].lower() if len(path) > 1 else None

def default_sort_rule(node: DAGNode):
    """
    Defines the default sort rule, intending to group like colors
    together as often as possible. The layout engine provided to
    mermaid may not always obey this order, but it works most of most
    of the time.
    """
    color = node.color if node.color is not None else ""
    return (node.slen, color, node.name)

def short_hash(inpt) -> str:
    """
    Generate a short hash for uniquely identifying `select` queries. This
    is similar to git's short hash in --abbrev-commit
    """
    hash_ = hashlib.sha1()
    hash_.update(str(inpt).encode('utf-8'))

    return hash_.hexdigest()[:6]

def read_config():
    """
    """
    default_path = pathlib.Path("~/.config/sql-visualizer/config")

    if default_path.expanduser().exists():
        config = configparser.ConfigParser()
        config.read(default_path.expanduser())

        return dict(config)

    return {}

def read_template(layout="elk") -> str:
    return f"""
        <!DOCTYPE html>
        <html lang="en">
        <head>
        <style>
            @media (prefers-color-scheme: dark) {{
                body {{
                    color: #c5c8c6;
                    background: #383d3f;
                }}
            }}

            html,
            body,
            #mermaid-container,
            .mermaid {{
                height: 100%;
            }}
        </style>
        </head>
        <body>
            <div id="mermaid-container">
                <pre class="mermaid">{{{{ MERMAID }}}}
                </pre>
            </div>
            <script type="module">
                import mermaid from 'https://cdn.jsdelivr.net/npm/mermaid@11/dist/mermaid.esm.min.mjs';
                import elkLayouts from 'https://cdn.jsdelivr.net/npm/@mermaid-js/layout-elk@0/dist/mermaid-layout-elk.esm.min.mjs';
                import panzoom from 'https://cdn.jsdelivr.net/npm/@panzoom/panzoom@4.6.1/+esm';

                mermaid.registerLayoutLoaders(elkLayouts);
                mermaid.initialize({{theme: 'neutral', layout: '{layout}'}});

                await mermaid.run({{
                    querySelector: '.mermaid',
                    postRenderCallback: (id) => {{
                        const cont = document.getElementById("mermaid-container");
                        const plot = cont.querySelector("svg");

                        const pz = panzoom(plot, {{
                            maxScale: 10,
                            minScale: 0.1,
                            step: 0.5}});

                        cont.addEventListener("wheel", pz.zoomWithWheel);
                    }}
                }});
            </script>
        </body>
        </html>
    """


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('infile')
    parser.add_argument('-d', '--dialect', nargs='?')
    parser.add_argument('-D', '--dagre', action='store_true')
    parser.add_argument('-s', '--serve', action='store_true')
    parser.add_argument('-S', '--show-subquery', action='store_true')

    args = parser.parse_args()
    path = pathlib.Path(args.infile)

    cfg = read_config()

    dialect = args.dialect or cfg.get('general', {}).get('dialect')
    colors = cfg.get('colors', {})

    # Dagre is a faster layout but I think it looks messier than ELK. Keep
    # the option to use the Dagre layout behind a flag.
    layout = 'dagre' if args.dagre else 'elk'

    ast_list = read_parse(path, dialect)

    dag = SimplifiedDAG()
    for ast in ast_list:
        node = process_ast(ast, args.show_subquery)

        if node is not None:
            dag.insert(node)

    dag.add_class_style(colors)
    dag.set_node_color_rule(default_color_rule)
    dag.sort(default_sort_rule)

    mermaid = dag.mm()

    if args.serve:
        # This is like a hack jinja
        template = read_template(layout)
        template = template.replace("{{ MERMAID }}", mermaid)

        with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.html', encoding='utf-8') as f:
            f.write(template)
            outfile = pathlib.Path(f.name)  

        webbrowser.open_new_tab(f"file://{outfile}")

    else:
        print(mermaid)
