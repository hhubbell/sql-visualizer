#!/usr/bin/env python
#
# Determine which tables are being referenced in a query
#

import argparse
import configparser
import hashlib
import pathlib
import tempfile
import webbrowser
import sqlglot


class DAGNode:
    
    def __init__(self, fqn):
        self.name = fqn
        self.sources = list()
        self.slen = 0
        self.id = None
        self.color = None

    def __iter__(self):
        for source in self.sources:
            yield source

            for sub in source:
                yield sub

    def add_source(self, source):
        self.sources.append(source)
        self.slen += 1

    def pairs(self):
        for source in self.sources:
            yield (source, self)

    def deep_pairs(self):
        for source in self.sources:
            yield (source, self)

            for sub in source.deep_pairs():
                yield sub


class SimplifiedDAG:

    def __init__(self):
        self.trees = list()
        self.next_id = 0
        self.colors = {
            "srcNode": "fill:#AACCD7,stroke:#666666",
            "intNode": "fill:#EEEEEE,stroke:#666666",
            "endNode": "fill:#FDE1A7,stroke:#666666"}

    def add_class_style(self, colors):
        """
        :param colors: classDef spec: {'class_name': 'fill:#HEXHEX[,etc];'}
        """
        self.colors.update(colors)

    def set_node_color_rule(self, callback):
        """
        Assign the color rule for all nodes
        :param callback: Color rule callable
        """
        for branch in self.trees:
            branch.color = callback(branch)

    def sort(self):
        self.trees.reverse()

    def pairs(self):
        for branch in self.trees:
            for pair in branch.pairs():
                yield pair

    def add_node(self, node):
        node.id = self.next_id

        self.trees.append(node)
        self.next_id += 1

    def root_nodes(self):
        seen = set()

        for branch in self.trees:
            for src in branch:
                if src.slen == 0 and src.name not in seen:
                    seen.add(src.name)
                    yield src

    def end_nodes(self):
        non_end = set()

        for branch in self.trees:
            for check in self.trees:
                if branch in check.sources:
                    non_end.add(branch)

        return set(self.trees) - non_end

    def insert(self, parent, children):
        self.add_node(parent)

        for child in children:
            if type(child) is not str:
                raise Exception("Inserting non string children not supported")

            known = None
            for branch in self.trees:
                if child == branch.name:
                    known = branch
                    break

            if known is None:
                known = DAGNode(child)
                self.add_node(known)

            parent.add_source(known)

    def mm(self):
        mmc = "\ngraph LR\n"

        node_class = {
            "srcNode": [],
            "intNode": [],
            "endNode": []}

        root_nodes = list(self.root_nodes())
        end_nodes = list(self.end_nodes())

        for branch in self.trees:
            mmc += f"""\t{branch.id}["{branch.name}"]\n"""

            if branch.color:
                if branch.color not in node_class:
                    node_class[branch.color] = []

                node_class[branch.color].append(branch.id)

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

def is_create(ast) -> bool:
    return type(ast) == sqlglot.exp.Create

def is_select(ast) -> bool:
    return type(ast) == sqlglot.exp.Select \
        or type(ast) == sqlglot.exp.Subquery \
        or type(ast) == sqlglot.exp.Union

def find_create(ast) -> set:
    objs = set()

    if is_create(ast):
        objs.add(ast.this.name.upper())

    return objs

def find_tables(ast) -> set:
    tables = set()

    # Probably a better way to descend this tree
    expr = ast.expression if is_create(ast) else ast

    if is_select(expr):
        ctes = {x.alias.upper() for x in expr.find_all(sqlglot.exp.CTE)}

        for table in expr.find_all(sqlglot.exp.Table):
            fqn = '.'.join(x.name.upper() for x in table.parts)

            if fqn not in ctes:
                tables.add(fqn)

    return tables

def default_color_rule(node):
    """
    Defines the default color rule for nodes styles. Can be overridden.
    """
    path = node.name.split('.')
    return path[0].lower() if len(path) > 1 else None

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
                    background: #1f1f1f;
                }}
            }}
        </style>
        </head>
        <body>
            <pre class="mermaid">{{{{ MERMAID }}}}
            </pre>
            <script type="module">
                import mermaid from 'https://cdn.jsdelivr.net/npm/mermaid@11/dist/mermaid.esm.min.mjs';
                import elkLayouts from 'https://cdn.jsdelivr.net/npm/@mermaid-js/layout-elk@0/dist/mermaid-layout-elk.esm.min.mjs';

                mermaid.registerLayoutLoaders(elkLayouts);
                mermaid.initialize({{theme: 'neutral', layout: '{layout}'}});
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

    args = parser.parse_args()
    path = pathlib.Path(args.infile)

    cfg = read_config()

    dialect = args.dialect or cfg.get('general', {}).get('dialect')
    colors = cfg.get('colors', {})

    # Dagre is a faster layout but I think it looks messier than ELK. Keep
    # the option to use the Dagre layout behind a flag.
    layout = 'dagre' if args.dagre else 'elk'

    ast_list = read_parse(path, args.dialect)

    dag = SimplifiedDAG()
    for ast in ast_list:
        if is_create(ast) or is_select(ast):
            creates = find_create(ast)
            sources = find_tables(ast)

            node = DAGNode(creates.pop() if creates else "Select#" + short_hash(ast))

            # DEBUG
            node.ast = ast

            dag.insert(node, sources)

    #dag.sort()
    dag.add_class_style(colors)
    dag.set_node_color_rule(default_color_rule)

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
