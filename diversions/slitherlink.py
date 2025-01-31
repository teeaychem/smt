import cvc5
import itertools

_ = None

grid = [
    [3, 3, _, _, _, 3, _],
    [_, _, 2, _, _, _, _],
    [_, _, _, 2, 1, _, 3],
    [2, 3, _, _, _, 0, 2],
    [0, _, 0, 3, _, _, _],
    [_, _, _, _, 0, _, _],
    [_, 3, _, _, _, 3, 3],
]


class Puzzle:
    def __init__(self, puzzle):
        self.puzzle = puzzle
        self.rows = len(puzzle[0])
        self.cols = len(puzzle)
        self.row_edges = self.rows + 1
        self.col_edges = self.cols + 1
        self.vertex_count = (self.row_edges) * (self.col_edges)

        self.tm = cvc5.TermManager()
        self.solver = cvc5.Solver(self.tm)
        self.solver.setOption("produce-models", "true")
        self.solver.setOption("finite-model-find", "true")
        self.solver.setLogic("ALL")

        self.edge_sort = self.tm.mkSetSort(
            self.tm.mkTupleSort(self.tm.getIntegerSort(), self.tm.getIntegerSort())
        )
        self.edges = self.tm.mkConst(self.edge_sort, "edges")

    def encoding_representation(self):
        """
        Returns a string displaying the encoding used for cells and verticies.
        Though, omitted from the encoding is that all edges are either left-right or top-bottom.
        """
        vertex = 0
        string = ""
        for row in range(self.row_edges):
            row_string = ""
            for col in range(self.col_edges):
                string += f"{vertex:2}"
                vertex += 1
                if col < self.col_edges - 1:
                    string += " --- "
                    row_string += f" |{row:2},{col:2}"

            string += "\n"

            if row < self.row_edges - 1:
                string += row_string + " | \n"

        return string

    def row_edge_pairs(self):
        """
        A generator for all row edges, as directed left-right edges.
        """
        v = 0
        while v < self.vertex_count:
            if (v + 1) % self.col_edges == 0:
                v += 1

            yield (v, v + 1)
            v += 1

    def col_edge_pairs(self):
        """
        A generator for all column edges, as directed top-bottom edges.
        """
        v = 0
        while v < self.vertex_count - self.row_edges:
            yield v, v + self.row_edges
            v += 1

    def all_edge_pairs(self):
        """
        A generator for all row and column edges.
        """
        return itertools.chain(self.row_edge_pairs(), self.col_edge_pairs())

    def top_edge(self, row, col):
        """
        The top edge of a cell.
        """
        row_offset = self.row_edges * row
        return (col + row_offset, col + row_offset + 1)

    def bottom_edge(self, row, col):
        """
        The bottom edge of a cell.
        """
        row_offset = self.row_edges * (row + 1)
        return (col + row_offset, col + row_offset + 1)

    def left_edge(self, row, col):
        """
        The left edge of a cell.
        """
        return (col + self.row_edges * row, col + self.row_edges * (row + 1))

    def right_edge(self, row, col):
        """
        The right edge of a cell.
        """
        return (col + self.row_edges * row + 1, col + self.row_edges * (row + 1) + 1)

    def cell_edges(self, row, col):
        """
        The edges of a cell.
        """
        return [
            self.top_edge(row, col),
            self.bottom_edge(row, col),
            self.left_edge(row, col),
            self.right_edge(row, col),
        ]

    def edge_term(self, edge):
        """
        An edge encoded as a term, specifically, as a pair of ints.
        """
        row = edge[0]
        col = edge[1]
        return self.tm.mkTuple([self.tm.mkInteger(row), self.tm.mkInteger(col)])

    def assert_edge(self, edge):
        """
        A term asserting that the given edge belongs to the edge relation.
        """
        return self.tm.mkTerm(cvc5.Kind.SET_MEMBER, self.edge_term(edge), self.edges)

    def assert_no_edge(self, edge):
        """
        A term asserting that the given edge does not belong to the edge relation.
        The negation of `assert_edge`
        """
        return self.tm.mkTerm(cvc5.Kind.NOT, self.assert_edge(edge))

    def a_edge_connections(self, edge):
        """
        Given an edge, returns the 'incoming' edges.
        """
        a = edge[0]
        b = edge[1]

        a_edges = []

        if a % self.col_edges != 0:
            a_left = (a - 1, a)
            a_edges.append(a_left)

        if a + self.row_edges == b and (a + 1) % self.col_edges != 0:
            a_right = (a, a + 1)
            a_edges.append(a_right)

        if a >= self.col_edges:
            a_up = (a - self.col_edges, a)
            a_edges.append(a_up)

        if a + 1 == b and (a + self.col_edges) < self.vertex_count:
            a_down = (a, a + self.col_edges)
            a_edges.append(a_down)

        return a_edges

    def b_edge_connections(self, edge):
        """
        Given an edge, returns the 'outgoing' edges.
        """
        a = edge[0]
        b = edge[1]

        b_edges = []

        if (b + 1) % self.col_edges != 0:
            b_right = (b, b + 1)
            b_edges.append(b_right)

        if b + self.col_edges <= self.vertex_count:
            b_down = (b, b + self.col_edges)
            b_edges.append(b_down)

        if a + 1 == b and (b - self.col_edges) >= 0:
            b_up = (b - self.col_edges, b)
            b_edges.append(b_up)

        if a + self.row_edges == b and b % self.col_edges != 0:
            b_left = (b - 1, b)
            b_edges.append(b_left)

        return b_edges

    def assert_cell_constraints(self):
        """
        Adds assertions detailing how many edges of a cell must be touched by a path.
        """
        for row in range(puzzle.rows):
            for col in range(puzzle.cols):
                requirement = puzzle.puzzle[row][col]

                edges = puzzle.cell_edges(row, col)

                match requirement:
                    case None:
                        pass

                    case 0:
                        for edge in edges:
                            self.solver.assertFormula(puzzle.assert_no_edge(edge))

                    case 1:
                        disjunction = []

                        for index in range(4):
                            exactly_one = self.tm.mkTerm(
                                cvc5.Kind.AND,
                                puzzle.assert_edge(edges[index]),
                                puzzle.assert_no_edge(edges[(index + 1) % 4]),
                                puzzle.assert_no_edge(edges[(index + 2) % 4]),
                                puzzle.assert_no_edge(edges[(index + 3) % 4]),
                            )
                            disjunction.append(exactly_one)

                        exactly_one_edge = self.tm.mkTerm(cvc5.Kind.OR, *disjunction)
                        self.solver.assertFormula(exactly_one_edge)

                    case 2:
                        disjunction = []

                        for index in range(4):
                            exactly_two_contiguous = self.tm.mkTerm(
                                cvc5.Kind.AND,
                                puzzle.assert_edge(edges[index]),
                                puzzle.assert_edge(edges[(index + 1) % 4]),
                                puzzle.assert_no_edge(edges[(index + 2) % 4]),
                                puzzle.assert_no_edge(edges[(index + 3) % 4]),
                            )
                            disjunction.append(exactly_two_contiguous)

                            exactly_two_one_step = self.tm.mkTerm(
                                cvc5.Kind.AND,
                                puzzle.assert_edge(edges[index]),
                                puzzle.assert_edge(edges[(index + 2) % 4]),
                                puzzle.assert_no_edge(edges[(index + 1) % 4]),
                                puzzle.assert_no_edge(edges[(index + 3) % 4]),
                            )
                            disjunction.append(exactly_two_one_step)

                        exactly_two_edges = self.tm.mkTerm(cvc5.Kind.OR, *disjunction)
                        self.solver.assertFormula(exactly_two_edges)

                    case 3:
                        disjunction = []

                        for index in range(4):
                            exactly_three = self.tm.mkTerm(
                                cvc5.Kind.AND,
                                puzzle.assert_edge(edges[index]),
                                puzzle.assert_edge(edges[(index + 1) % 4]),
                                puzzle.assert_edge(edges[(index + 2) % 4]),
                                puzzle.assert_no_edge(edges[(index + 3) % 4]),
                            )
                            disjunction.append(exactly_three)

                        exactly_three_edges = self.tm.mkTerm(cvc5.Kind.OR, *disjunction)
                        self.solver.assertFormula(exactly_three_edges)

                    case _:
                        print("Unexpected cell constraints")
                        exit(1)

    def assert_path_constriants(self):
        """
        Adds conditionals stating that if a path is along some edge, then the path continues to exactly one connecting edge.
        """
        for edge in puzzle.all_edge_pairs():

            def constrain_edges(ab_edges):
                """
                A helper function, as the constraints are general over incoming/outgoing edges.
                """
                if len(ab_edges) == 1:
                    self.solver.assertFormula(
                        self.tm.mkTerm(
                            cvc5.Kind.IMPLIES,
                            puzzle.assert_edge(edge),
                            puzzle.assert_edge(ab_edges[0]),
                        )
                    )
                else:
                    one_edge_conjunction = []
                    edge_count = len(ab_edges)
                    for index in range(edge_count):
                        unique_edge = [puzzle.assert_edge(ab_edges[index])]

                        for offset in range(1, edge_count):
                            other_index = (index + offset) % edge_count
                            unique_edge.append(
                                puzzle.assert_no_edge(ab_edges[other_index])
                            )

                        one_edge_conjunction.append(
                            self.tm.mkTerm(cvc5.Kind.AND, *unique_edge)
                        )

                    unique_a_implication = self.tm.mkTerm(
                        cvc5.Kind.IMPLIES,
                        puzzle.assert_edge(edge),
                        self.tm.mkTerm(cvc5.Kind.OR, *one_edge_conjunction),
                    )

                    self.solver.assertFormula(unique_a_implication)

            constrain_edges(puzzle.a_edge_connections(edge))
            constrain_edges(puzzle.b_edge_connections(edge))

    def solve(self):
        """
        Solves a puzzle by adding constraints and then discarding models until a model with a unique path is found.
        """
        self.assert_cell_constraints()
        self.assert_path_constriants()

        while True:
            result = self.solver.checkSat()
            if result.isUnsat():
                print("Could not find a solution")
                exit(1)


            # Given a model, read the edge relation and recursively parse the set to a list
            edges_found = self.solver.getValue(self.edges)
            edge_list = list()

            # Assume the parse tree always has a set element on the left branch and the remaining set on the right branch
            while edges_found.getNumChildren() == 2:
                left = edges_found[0]
                right = edges_found[1]

                edge_list.append((left[0][1], left[0][2]))

                edges_found = right

            edge_list.append((edges_found[0][1], edges_found[0][2]))

            # Take some edge, and then continually take from the set a connecting edge
            on_edge = edge_list.pop()

            while on_edge:
                edge_a = on_edge[0]
                edge_b = on_edge[1]
                on_edge = None

                for index, other_edge in enumerate(edge_list):
                    if edge_a in other_edge or edge_b in other_edge:
                        on_edge = edge_list.pop(index)

            # If every edge has been seen, there was a unique path
            # Otherwise, block the model and go again.
            if len(edge_list) == 0:
                print("Solution:")
                print(self.path_representation())
                exit(0)
            else:
                self.solver.blockModel(cvc5.BlockModelsMode.LITERALS)

    def path_representation(self):
        """
        Returns a string representing a path.
        Assumes solve has been called and has returned sat.
        """
        path_string = ""

        for row in range(self.rows):
            above_string = ""
            col_string = ""

            for col in range(self.cols):
                top = self.assert_edge(self.top_edge(row, col))
                if self.solver.getValue(top) == self.tm.mkTrue():
                    above_string += "---"
                else:
                    above_string += "   "

                left = self.assert_edge(self.left_edge(row, col))
                if self.solver.getValue(left) == self.tm.mkTrue():
                    col_string += "|  "
                else:
                    col_string += "   "

            bottom = self.assert_edge(self.right_edge(row, col))
            if self.solver.getValue(bottom) == self.tm.mkTrue():
                col_string += "|"
            else:
                col_string += " "

            path_string += above_string + "\n"
            path_string += col_string + "\n"

        below_string = ""

        for col in range(self.cols):
            right = self.assert_edge(self.bottom_edge(self.rows - 1, col))
            if self.solver.getValue(right) == self.tm.mkTrue():
                below_string += "---"
            else:
                below_string += "   "

        path_string += below_string

        return path_string


puzzle = Puzzle(grid)
puzzle.solve()
