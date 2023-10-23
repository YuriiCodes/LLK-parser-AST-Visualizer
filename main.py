import networkx as nx
import matplotlib.pyplot as plt


class Grammar:
    def __init__(self, rules):
        self.rules = rules
        self.non_terminals = list(rules.keys())
        self.terminals = self.get_terminals()

    def get_terminals(self):
        terminals = set()
        for productions in self.rules.values():
            for production in productions:
                for symbol in production:
                    if symbol not in self.non_terminals:
                        terminals.add(symbol)
        return list(terminals)


# Task 1  -  First (k)
def compute_first(grammar, symbol, first_cache):
    """Compute the FIRST set for a given symbol."""
    if symbol in first_cache:
        return first_cache[symbol]

    # Initialize the result set
    first_set = set()

    # If the symbol is a terminal, add it to the FIRST set
    if symbol in grammar.terminals:
        first_set.add(symbol)
        first_cache[symbol] = first_set
        return first_set

    for production in grammar.rules[symbol]:
        if production == 'ε':  # epsilon
            first_set.add('ε')
        else:
            for s in production:
                first_s = compute_first(grammar, s, first_cache)
                first_set.update(first_s - {'ε'})
                if 'ε' not in first_s:
                    break
            else:
                first_set.add('ε')

    first_cache[symbol] = first_set
    return first_set

# Task 1  -  Follow (k)
def compute_follow(grammar, symbol, first_cache, follow_cache):
    """Compute the FOLLOW set for a given non-terminal."""
    if symbol in follow_cache:
        return follow_cache[symbol]

    follow_set = set()

    # Start symbol always has $ in its FOLLOW set
    if symbol == grammar.non_terminals[0]:
        follow_set.add('$')

    for non_terminal, productions in grammar.rules.items():
        for production in productions:
            if symbol in production:
                idx = production.index(symbol)
                if idx + 1 < len(production):
                    first_next = compute_first(grammar, production[idx + 1], first_cache)
                    follow_set.update(first_next - {'ε'})
                    if 'ε' in first_next:
                        follow_set.update(compute_follow(grammar, non_terminal, first_cache, follow_cache))
                else:
                    follow_set.update(compute_follow(grammar, non_terminal, first_cache, follow_cache))

    follow_cache[symbol] = follow_set
    return follow_set


# Example: Arithmetic grammar
arithmetic_grammar = Grammar({
    'E': ['TE\''],
    'E\'': ['+TE\'', 'ε'],
    'T': ['FT\''],
    'T\'': ['*FT\'', 'ε'],
    'F': ['(E)', 'id']
})


def build_parsing_table(grammar, first_sets, follow_sets):
    """Build the LL(1) parsing table for a given grammar."""
    parsing_table = {}

    for non_terminal, productions in grammar.rules.items():
        for production in productions:
            # For each terminal in FIRST(production)
            first_production = set()
            for symbol in production:
                first_symbol = first_sets[symbol] if symbol in first_sets else {symbol}
                first_production.update(first_symbol - {'ε'})
                if 'ε' not in first_symbol:
                    break
            else:
                first_production.add('ε')

            for terminal in first_production:
                if terminal != 'ε':
                    if (non_terminal, terminal) not in parsing_table:
                        parsing_table[(non_terminal, terminal)] = production
                    else:
                        raise ValueError(f"Grammar is not LL(1): Conflict at ({non_terminal}, {terminal})")

            # If ε is in FIRST(production), for each terminal in FOLLOW(non_terminal)
            if 'ε' in first_production:
                for terminal in follow_sets[non_terminal]:
                    if (non_terminal, terminal) not in parsing_table:
                        parsing_table[(non_terminal, terminal)] = production
                    else:
                        raise ValueError(f"Grammar is not LL(1): Conflict at ({non_terminal}, {terminal})")

    return parsing_table


# Task 2 - Epsilon producing non-terminals
def find_epsilon_producing_non_terminals(grammar):
    """Find non-terminals that can produce epsilon."""
    epsilon_producers = set()

    # Initial pass: find non-terminals with direct epsilon productions
    for non_terminal, productions in grammar.rules.items():
        if 'ε' in productions:
            epsilon_producers.add(non_terminal)

    # Iteratively find non-terminals that can produce epsilon through other non-terminals
    changed = True
    while changed:
        changed = False
        for non_terminal, productions in grammar.rules.items():
            for production in productions:
                if all(symbol in epsilon_producers for symbol in production):
                    if non_terminal not in epsilon_producers:
                        epsilon_producers.add(non_terminal)
                        changed = True
                        break

    return epsilon_producers

# Task 2  -  read grammar from text
def parse_grammar_from_text(text):
    """Parse a grammar from the given text format."""
    rules = {}
    lines = text.strip().split('\n')

    for line in lines:
        lhs, rhs = line.split('→')
        lhs = lhs.strip()
        productions = [production.strip() for production in rhs.split('|')]
        rules[lhs] = productions

    return Grammar(rules)



# Аналізатор методом рекурсивного спуску
class RecursiveDescentParser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.current_token_index = 0

    def look_ahead(self):
        if self.current_token_index < len(self.tokens):
            return self.tokens[self.current_token_index]
        return None

    def consume(self, expected_token):
        if self.look_ahead() == expected_token:
            self.current_token_index += 1
            return True
        return False

    # Grammar rules implementation
    def E(self):
        if self.T():
            if self.E_prime():
                return True
        return False

    def E_prime(self):
        if self.consume('+'):
            if self.T():
                if self.E_prime():
                    return True
            return False
        return True  # epsilon

    def T(self):
        if self.F():
            if self.T_prime():
                return True
        return False

    def T_prime(self):
        if self.consume('*'):
            if self.F():
                if self.T_prime():
                    return True
            return False
        return True  # epsilon

    def F(self):
        if self.consume('('):
            if self.E():
                if self.consume(')'):
                    return True
            return False
        elif self.consume('id'):
            return True
        return False

    def parse(self):
        return self.E() and self.current_token_index == len(self.tokens)


# Візуалізація АСД
class Node:
    def __init__(self, type, children=None, value=None):
        self.type = type
        self.children = children or []
        self.value = value


class ASTRecursiveDescentParser(RecursiveDescentParser):

    # Overriding grammar rules to build AST
    def E(self):
        t_node = self.T()
        if t_node:
            e_prime_node = self.E_prime()
            if e_prime_node:
                return Node('E', [t_node, e_prime_node])
        return None

    def E_prime(self):
        if self.consume('+'):
            t_node = self.T()
            if t_node:
                e_prime_node = self.E_prime()
                if e_prime_node:
                    return Node("E'", [Node('op', value='+'), t_node, e_prime_node])
        return Node("E'", [Node('ε')])

    def T(self):
        f_node = self.F()
        if f_node:
            t_prime_node = self.T_prime()
            if t_prime_node:
                return Node('T', [f_node, t_prime_node])
        return None

    def T_prime(self):
        if self.consume('*'):
            f_node = self.F()
            if f_node:
                t_prime_node = self.T_prime()
                if t_prime_node:
                    return Node("T'", [Node('op', value='*'), f_node, t_prime_node])
        return Node("T'", [Node('ε')])

    def F(self):
        if self.consume('('):
            e_node = self.E()
            if e_node and self.consume(')'):
                return Node('F', [e_node])
        elif self.consume('id'):
            return Node('F', [Node('id')])
        return None

    def parse(self):
        ast_root = self.E()
        if ast_root and self.current_token_index == len(self.tokens):
            return ast_root
        return None



def visualize_ast(node, graph=None, parent_name=None, node_name=None):
    """Recursively visualize an AST using networkx and matplotlib."""
    if graph is None:
        graph = nx.DiGraph()
        node_name = node.type

    graph.add_node(node_name, label=node.value or node.type)
    if parent_name:
        graph.add_edge(parent_name, node_name)

    for child in node.children:
        child_name = f"{child.type}_{id(child)}"
        visualize_ast(child, graph, node_name, child_name)

    return graph

# LL(k) аналізатор для k>1 = +6 балів
def compute_first_k(grammar, sequence, k, first_cache):
    """Compute the FIRST_k set for a given sequence of symbols."""
    first_k_set = set()

    if not sequence:
        first_k_set.add('ε')
        return first_k_set

    # If sequence has only one symbol, delegate to compute_first
    if len(sequence) == 1:
        first_1_set = compute_first(grammar, sequence[0], first_cache)
        for item in first_1_set:
            if item != 'ε':
                first_k_set.add(item[:k])
            else:
                first_k_set.add('ε')
        return first_k_set

    # Compute FIRST_k for longer sequences
    for i, symbol in enumerate(sequence):
        first_i = compute_first(grammar, symbol, first_cache)
        new_items = set()

        # Combine with previously found items in first_k_set
        for item_prev in first_k_set:
            for item_cur in first_i:
                if item_cur != 'ε':
                    combined = (item_prev + item_cur)[:k]
                    new_items.add(combined)

        # If ε is in FIRST of the current symbol, continue with the next symbol
        if 'ε' in first_i:
            new_items.add('ε')
        else:
            first_k_set = new_items
            break

        first_k_set = new_items

    return first_k_set


def build_parsing_table_k(grammar, first_k_sets, follow_sets, k):
    """Build the LL(k) parsing table for a given grammar."""
    parsing_table = {}

    for non_terminal, productions in grammar.rules.items():
        for production in productions:
            first_k_production = compute_first_k(grammar, production, k, first_k_sets)
            for lookahead_seq in first_k_production:
                if lookahead_seq != 'ε':
                    if (non_terminal, lookahead_seq) not in parsing_table:
                        parsing_table[(non_terminal, lookahead_seq)] = production
                    else:
                        raise ValueError(f"Grammar is not LL({k}): Conflict at ({non_terminal}, {lookahead_seq})")

            # If ε is in FIRST_k(production), for each terminal in FOLLOW(non_terminal)
            if 'ε' in first_k_production:
                for terminal in follow_sets[non_terminal]:
                    # We only consider the first symbol from FOLLOW for building LL(k) table
                    if (non_terminal, terminal[0]) not in parsing_table:
                        parsing_table[(non_terminal, terminal[0])] = production
                    else:
                        raise ValueError(f"Grammar is not LL({k}): Conflict at ({non_terminal}, {terminal[0]})")

    return parsing_table

def main():
    # Compute FIRST and FOLLOW sets for the example
    first_cache = {}
    follow_cache = {}

    first_sets = {nt: compute_first(arithmetic_grammar, nt, first_cache) for nt in arithmetic_grammar.non_terminals}
    follow_sets = {nt: compute_follow(arithmetic_grammar, nt, first_cache, follow_cache) for nt in arithmetic_grammar.non_terminals}
    print("first_sets")
    print(first_sets)
    print("follow_sets")
    print(follow_sets)

    parsing_table = build_parsing_table(arithmetic_grammar, first_sets, follow_sets)
    print("parsing_table")
    print(parsing_table)

    epsilon_producing_non_terminals = find_epsilon_producing_non_terminals(arithmetic_grammar)
    print("epsilon_producing_non_terminals")
    print(epsilon_producing_non_terminals)

    # Test the function
    sample_grammar_text = """
    E → TE'
    E' → +TE' | ε
    T → FT'
    T' → *FT' | ε
    F → (E) | id
    """


    parsed_grammar = parse_grammar_from_text(sample_grammar_text)
    print("parsed_grammar.rules")
    print(parsed_grammar.rules)

    print("manually set grammar rules (just to make sure parsing works)")
    print(arithmetic_grammar.rules)


    # Аналізатор методом рекурсивного спуску
    sample_tokens = ['(', 'id', '+', 'id', ')', '*', 'id']
    parser = RecursiveDescentParser(sample_tokens)
    parse_result = parser.parse()
    print("parse_result")
    print(parse_result)

    # Test the AST building parser
    ast_parser = ASTRecursiveDescentParser(sample_tokens)
    ast_root = ast_parser.parse()

    # Visualize the AST
    ast_graph = visualize_ast(ast_root)
    pos = nx.spring_layout(ast_graph)
    labels = {node: data['label'] for node, data in ast_graph.nodes(data=True)}

    '''
    Візуалізоване абстрактне синтаксичне дерево (AST) для виразу 
    (id + id) × id
    (id+id)×id на основі нашої арифметичної граматики.
    Дерево відображає структуру виразу згідно з правилами граматики. 
    Термінальні символи (такі як id, + та *) представлені як листя дерева,
     тоді як нетермінальні символи (такі як 
    E, T тощо) представлені як внутрішні вузли.
    Тепер у нас є візуалізація AST для арифметичних виразів. 
    '''
    plt.figure(figsize=(10, 6))
    nx.draw(ast_graph, pos, labels=labels, with_labels=True, node_size=3000, node_color="skyblue")
    plt.title("Abstract Syntax Tree (AST)")
    plt.show()

    # LL(k) аналізатор для k > 1
    first_k_cache = {}
    first_k_sets = {nt: compute_first_k(arithmetic_grammar, [nt], 2, first_k_cache) for nt in
                    arithmetic_grammar.non_terminals}
    print("first_k_sets")
    print(first_k_sets)

    ll2_grammar_rules = {
        'S': ['aAd', 'bBd', 'aBe', 'bAe'],
        'A': ['c'],
        'B': ['c']
    }

    ll2_grammar = Grammar(ll2_grammar_rules)

    # Compute FIRST_k sets again
    first_k_cache_ll2 = {}
    first_k_sets_ll2 = {nt: compute_first_k(ll2_grammar, [nt], 2, first_k_cache_ll2) for nt in
                        ll2_grammar.non_terminals}







    follow_cache_ll2 = {}
    follow_sets_ll2 = {nt: compute_follow(ll2_grammar, nt, first_k_cache_ll2, follow_cache_ll2) for nt in
                       ll2_grammar.non_terminals}


    parsing_table_ll2 = build_parsing_table_k(ll2_grammar, first_k_sets_ll2, follow_sets_ll2, 2)
    print("parsing_table_ll2")
    print(parsing_table_ll2)


if __name__ == '__main__':
    main()