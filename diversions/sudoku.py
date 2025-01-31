import cvc5.pythonic as smt


class Puzzle:
    empty_puzzle = [[0 for _ in range(9)] for _ in range(9)]

    def atom_grid(self):
        grid = []
        for row in range(9):
            row_atoms = []
            for col in range(9):
                row_atoms.append(smt.Int(f"Cell({row + 1},{col + 1})"))
            grid.append(row_atoms)

        return grid

    def __init__(self):
        self.puzzle = self.empty_puzzle

        self.cell_atoms = self.atom_grid()

    def set_value(self, row, col, val):
        self.puzzle[row - 1][col - 1] = val

    def get_value(self, row, col):
        return self.puzzle[row - 1][col - 1]

    def get_atom(self, row, col):
        return self.cell_atoms[row - 1][col - 1]

    def __str__(self):
        string = ""

        for row in self.puzzle:
            for cell in row:
                if cell != 0:
                    string += str(cell)
                else:
                    string += "_"
                string += " "
            string += "\n"

        return string


def cells(row_max, col_max):
    row = 1
    col = 1
    while row <= row_max and col <= col_max:
        yield (row, col)

        if col == col_max:
            col = 1
            row += 1
        else:
            col += 1


def solve(puzzle):
    solver = smt.Solver()

    for row, col in cells(9, 9):
        solver.add(
            smt.And(1 <= puzzle.get_atom(row, col), puzzle.get_atom(row, col) <= 9)
        )

    for row in puzzle.cell_atoms:
        solver.add(smt.Distinct(row))

    for col in range(9):
        column = [puzzle.get_atom(row, col) for row in range(9)]
        solver.add(smt.Distinct(column))

    for block_row in range(3):
        for block_col in range(3):
            block = []
            for row in range(1, 4):
                for col in range(1, 4):
                    block.append(
                        puzzle.get_atom(row + block_row * 3, col + block_col * 3)
                    )
            solver.add(smt.Distinct(block))

    for row, col in cells(9, 9):
        if puzzle.get_value(row, col) != 0:
            solver.add(puzzle.get_atom(row, col) == puzzle.get_value(row, col))


    match solver.check():
        case smt.sat:
            model = solver.model()
            for row, col in cells(9, 9):
                puzzle.set_value(row, col, model.eval(puzzle.get_atom(row, col)).as_long())
        case other:
            print(other)
            exit(1)


puzzle = Puzzle()
puzzle.set_value(1, 1, 5)
puzzle.set_value(1, 2, 3)
puzzle.set_value(1, 5, 7)

puzzle.set_value(2, 1, 6)
puzzle.set_value(2, 4, 1)
puzzle.set_value(2, 5, 9)
puzzle.set_value(2, 6, 5)

puzzle.set_value(3, 2, 9)
puzzle.set_value(3, 3, 8)
puzzle.set_value(3, 8, 6)

puzzle.set_value(4, 1, 8)
puzzle.set_value(4, 5, 6)
puzzle.set_value(4, 9, 3)

puzzle.set_value(5, 1, 4)
puzzle.set_value(5, 4, 8)
puzzle.set_value(5, 6, 3)
puzzle.set_value(5, 9, 1)

puzzle.set_value(6, 1, 7)
puzzle.set_value(6, 5, 2)
puzzle.set_value(6, 9, 6)

puzzle.set_value(7, 2, 6)
puzzle.set_value(7, 7, 2)
puzzle.set_value(7, 8, 8)

puzzle.set_value(8, 4, 4)
puzzle.set_value(8, 5, 1)
puzzle.set_value(8, 6, 9)
puzzle.set_value(8, 9, 5)

puzzle.set_value(9, 5, 8)
puzzle.set_value(9, 8, 7)
puzzle.set_value(9, 9, 9)


solve(puzzle)
print(puzzle)
