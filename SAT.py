# SAT is a Satisfiability Solver, in this case for SUDOKU's
# made by Group 30: Melda Malkoc, Imtiaz Nazar Ali, Roel Rotteveel, Dana Weenink
# last edited on 9/25/2020

import sys
import math
import random
import json
from itertools import chain
from collections import Counter

# Arguments from input line
DPtype = sys.argv[1]
file = sys.argv[2]
file = open(sys.argv[2], "r")
endList = []
numberbacktracks = 0

# Decide which program to run. If both not true, run 'normal' DP
heuristic1 = False
heuristic2 = False
heuristic3 = False

if DPtype == "-S2":
    heuristic1 = True
    print("Heuristic 1:", heuristic1)
elif DPtype == "-S3":
    heuristic2 = True
    print("Heuristic 2:", heuristic2)
elif DPtype == "-S4":
    heuristic3 = True
    print("Heuristic 3:", heuristic3)
else:
    print("Basic DPLL")

lengthList = 81  # default for 9x9 sudoku
widthSudoku = 9  # default for 9x9 sudoku
nr_of_knowns = 0 # counter for the amount of known numbers of the sudoku from the file


def sudoku2DIMACS(file):
    global lengthList
    global widthSudoku
    global nr_of_knowns

    sudoku = file.readline()

    sudokuList = list(sudoku)
    lengthList = len(sudokuList)
    widthSudoku = int(math.sqrt(lengthList))


    # While a next line can be read, for processing multiple Sudoku's
    while sudoku:

        # Loop over sudokuList and keep track of y & x coordinates
        x = 1
        y = 1
        for i in range(lengthList):
            if not sudokuList[i] == '.':
                nr_of_knowns +=1
                # Write to output file
                with open(file_out, 'a') as the_file:
                    the_file.write('{}{}{} {}\n'.format(y, x, sudokuList[i], 0))
            # make sure x and y are updated correctly
            if x == widthSudoku:
                x = 1
                y += 1
            else:
                x += 1
        # read next line
        with open(file_out, 'a') as the_file:
            the_file.write('\n')
        sudoku = file.readline()

    print("Amount of numbers already known:",nr_of_knowns)

    file.close()


file_out = '{}_DIMACS.txt'.format(sys.argv[2])
# clean output file if it exists alreadyt:
clean_inhoud = open(file_out, "w")
clean_inhoud.close()

# encode sudoku to DIMACS format
sudoku2DIMACS(file)


# Merge DIMACS sudokufile (one sudoku) with the sudoku rules file into "sudoku-plus-rules.txt"
def MergeRulesAndSudokuDIMACS(sudokufile, rulesfile):
    with open(sudokufile) as sudoku_file:
        sudoku = sudoku_file.read() #remove additional enter ("/n") at the end of the DIMACS later
    with open(rulesfile) as sudoku_rules_file:
        firstline = sudoku_rules_file.readline()
        next(sudoku_rules_file)
        sudoku_rules = sudoku_rules_file.read()

    sudoku_plus_rules = firstline + sudoku + sudoku_rules

    with open("sudoku-plus-rules.txt", "w") as sudoku_plus_rules_out:
        sudoku_plus_rules_out.write(sudoku_plus_rules)


MergeRulesAndSudokuDIMACS(file_out, "sudoku-rules.txt")
file = open("sudoku-plus-rules.txt", "r")


# Creates a 2D list from DIMACS input file
def DIMACS2Lists(file):
    listD = []
    line = file.readline()
    while line:
        lineSplit = line.split()  # split line into list
        if len(lineSplit) != 0 and (lineSplit[0] != ("p" or "c")):  # Check if line interesting
            lineSplit = list(map(int, lineSplit))  # makes integers from every item in list, returns that list
            lineSplit = lineSplit[:-1]  # delete last item since this is always 0
            listD.append(lineSplit)
        line = file.readline()
    return listD  # list of lists containing integers

unit_literal_number = 0
# Simplifies the set of clauses.
def simplification(serial_a, literal, serial_certainList):
    global unit_literal_number
    a = json.loads(serial_a)  # deserialize
    received_certainList = json.loads(serial_certainList)  # deserialize

    # Delete all instance of '-literal', or add to certainList
    # Go over all clauses
    for sublijst in a:
        for letter in sublijst:
            # remove if negative instance of literal
            if (letter == -literal):
                sublijst.remove(letter)
            # else if letter is found add to certainList
            elif (letter == literal):
                if letter not in received_certainList and letter > 0:
                    received_certainList.append(letter)

    # Delete all clauses with literal in it
    a[:] = [sublist for sublist in a if all(x != literal for x in sublist)]

    # check for other unit clauses. If found return simplification with unit clause
    for sublijst in a:
        if len(sublijst) == 1:
            if sublijst[0] > 0:
                unit_literal_number+=1
            serial_alpha = json.dumps(a)
            serial_certainList = json.dumps(received_certainList)
            return simplification(serial_alpha, sublijst[0], serial_certainList)

    # if all clauses have been deleted the set is satisfied. Return True for DPLL2
    if len(a) == 0:
        global endList
        endList = received_certainList  # save the answer in endList
        serial_alpha = json.dumps(a)
        serial_certainList = json.dumps(received_certainList)
        return True, serial_alpha, serial_certainList
    # if one clause is empty unsatisfiable. Return False for DPLL2
    elif [] in a:
        serial_alpha = json.dumps(a)
        serial_certainList = json.dumps(received_certainList)
        return False, serial_alpha, serial_certainList

    # If code comes here, alpha is maximally simplified with given literals.
    # Return None and simplify further with new literals from DPLL2
    serial_alpha = json.dumps(a)
    serial_certainList = json.dumps(received_certainList)
    return None, serial_alpha, serial_certainList


# Davis Putnam. 1) Simplifies and 2) Solves SAT
def dpll_2(serial_cnf, literal, serial_certainList):
    global heuristic1
    global heuristic2
    global heuristic3
    global numberbacktracks

    # 1) Simplify
    trueNoneFalse, serial_cnf, serial_certainList = simplification(serial_cnf, literal, serial_certainList)

    # 1.1) Check if Solved
    if (trueNoneFalse == True):
        return True
    elif (trueNoneFalse == False):
        return False

    # () unpack serialized cnf to choose literal
    received_cnf = json.loads(serial_cnf)
    # 2.1) Choose literal
    #-S2
    if heuristic1:
        P = Jeroslow_Wang(received_cnf)

    elif heuristic2:
        P = DLCS(received_cnf)

    elif heuristic3:
        P = DLIS(received_cnf)
    else:
        P = Choose_Random_Literal(received_cnf)

    # () serialize cnf again
    serial_cnf = json.dumps(received_cnf)

    # 2) Head into recursion
    if (dpll_2(serial_cnf, -1 * P, serial_certainList)):
        return True
    else:
        numberbacktracks +=1
        return dpll_2(serial_cnf, P, serial_certainList)

# choosing a literal from all clauses: avoid local maxima
def Choose_Random_Literal(cnf):
    if (cnf):
        sublist = random.choice(cnf)
        literal = random.choice(sublist)
        return literal


def Jeroslow_Wang(cnf):
    global widthSudoku

    if not cnf:
        return None
#VAR
    list = {}
    optimal_literal = 0
    maximum_value = -1


#compare clauses and return optimal literal
    for i in range(len(cnf)):
        for literal in cnf[i]:
            add_to_set(list, cnf, literal, i)
            optimal_literal = return_max_value(list, literal, maximum_value)
    if optimal_literal == 0:
        raise Exception("error, no clauses")
    return optimal_literal

#Calculating Value J(I)= sum over 2 to the power of length of clause
def add_to_set(list, cnf, x, i):
    if x in list:
        list[x] += 2 ** (-len(cnf[i]))
    else:
        list[x] = 2 ** (-len(cnf[i]))

#select literal with highest value J, part of one-sided Jeroslow-Wang
def return_max_value(list, literal, maximum_value):
    if -literal not in list:
        list[-literal] = 0
    if (list[literal] + list[-literal]) > maximum_value:
        maximum_value = list[literal] + list[-literal]
        if list[literal] >= list[-literal]:
            optimal_literal = literal
        else:
            optimal_literal = -literal
    elif list[literal] > maximum_value:
        maximum_value = list[literal]
        optimal_literal = literal
    return optimal_literal


def DLCS(cnf):
	global widthSudoku
	#Create dict to save the literal with maximum occurances in the cnf.
	max_literal = {'literal': '', 'count': 0}

	# All possible literals
	for x in range(1, widthSudoku + 1):
		for y in range(1, widthSudoku + 1):
			for z in range(1, widthSudoku + 1):

				pos_literal = int('{}{}{}'.format(x,y,z))
				neg_literal = -pos_literal

				pos_count = 0
				neg_count = 0

				# Count the number of times the positive and negative of a literal occur in cnf.
				for sublist in cnf:
					if pos_literal in sublist:
						pos_count += 1
					if neg_literal in sublist:
						neg_count += 1

				total_count = pos_count + neg_count
				# Determine which (pos/neg) literal has the highest count
				# and if the positive or the negative version of the literal occurs more often.
				# This is the literal used for the next dpll run.
				if total_count > max_literal['count']:
					if pos_count >= neg_count:
						max_literal['literal'] = pos_literal
						max_literal['count'] = total_count

					if neg_count > pos_count:
						max_literal['literal'] = neg_literal
						max_literal['count'] = total_count
	return max_literal['literal']

#find the literal with most occurence
def DLIS(cnf):
    i=0
    for sublijst in cnf:
        if sublijst:
            i+=1
    if i!=0:
        return Counter(chain.from_iterable(cnf)).most_common(1)[0][0]
    else:
        return None

# prints the final solution. Only works for 9x9!
def printEndList():
    global lengthList
    global widthSudoku
    global endList

    # name DIMACS output file
    output_file = '{}.out'.format(sys.argv[2])
    # Clean output file if it exists already
    clean_outfile = open(output_file, "w")
    clean_outfile.close()

    endList = [x for x in endList if x > 0]  # delete all negative numbers:
    endList = list(set(endList))  # delete doubles
    endList.sort()  # sort

    for i in range(lengthList):  # print as DIMACS to output file
        with open(output_file, 'a') as created_file:
            created_file.write('{} {}\n'.format(endList[i], 0))

    for i in range(lengthList):
        endList[i] = endList[i] % 10

    k = 0
    l = widthSudoku
    for i in range(widthSudoku):
        print(endList[k:l])
        k += widthSudoku
        l += widthSudoku

    endList.clear()


def main():
    # 1: make one big list with all the lines in there
    superList = DIMACS2Lists(file)

    # 2: find first unit clause
    certainList = []
    for sublist in superList:
        if len(sublist) == 1:  # if list of one integer
            certainList.append(sublist[0])
            break

    # (): serialize lists. Otherwise not correctly returned after faulty recursion
    serial_superList = json.dumps(superList)
    serial_certainList = json.dumps(certainList)

    # 3: apply dpll to remaining sudoku rules
    if dpll_2(serial_superList, certainList[0], serial_certainList):
        print("dpll = true")
        printEndList()
    else:
        print("dpll = false")
    print("--------------------------------------Number of backtracks:", numberbacktracks)


# assures main is executed when file is called
if __name__ == "__main__":
    main()