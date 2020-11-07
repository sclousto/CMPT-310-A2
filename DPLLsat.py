#!/usr/bin/python3
# CMPT310 A2
#####################################################
#####################################################
# Please enter the number of hours you spent on this
# assignment here
"""
num_hours_i_spent_on_this_assignment = 10
"""
#
#####################################################
#####################################################

#####################################################
#####################################################
# Give one short piece of feedback about the course so far. What
# have you found most interesting? Is there a topic that you had trouble
# understanding? Are there any changes that could improve the value of the
# course to you? (We will anonymize these before reading them.)
"""
Having to use linux for this assignment was kind of a pain especially considering it's very hard to know if your algorithm is fast enough while runningn on a virtual machine.

Otherwise the course is going great!

"""
#####################################################
#####################################################
import sys, getopt
import copy
import random
import time
import numpy as np
sys.setrecursionlimit(10000)

class SatInstance:
    def __init__(self):
        pass

    def from_file(self, inputfile):
        self.clauses = list()
        self.VARS = list()
        self.p = 0
        self.cnf = 0
        with open(inputfile, "r") as input_file:
            self.clauses.append(list())
            maxvar = 0
            for line in input_file:
                tokens = line.split()
                if len(tokens) != 0 and tokens[0] not in ("p", "c"):
                    for tok in tokens:
                        lit = int(tok)
                        maxvar = max(maxvar, abs(lit))
                        if lit == 0:
                            self.clauses.append(list())
                        else:
                            self.clauses[-1].append(lit)
                if tokens[0] == "p":
                    self.p = int(tokens[2])
                    self.cnf = int(tokens[3])
            assert len(self.clauses[-1]) == 0
            self.clauses.pop()
            if (maxvar > self.p):
                print("Non-standard CNF encoding!")
                sys.exit(5)
        # Variables are numbered from 1 to p
        for i in range(1, self.p + 1):
            self.VARS.append(i)

    def __str__(self):
        s = ""
        for clause in self.clauses:
            s += str(clause)
            s += "\n"
        return s


def main(argv):
    inputfile = ''
    verbosity = False
    inputflag = False
    try:
        opts, args = getopt.getopt(argv, "hi:v", ["ifile="])
    except getopt.GetoptError:
        print('DPLLsat.py -i <inputCNFfile> [-v] ')
        sys.exit(2)
    for opt, arg in opts:
        if opt == '-h':
            print('DPLLsat.py -i <inputCNFfile> [-v]')
            sys.exit()
        ##-v sets the verbosity of informational output
        ## (set to true for output veriable assignments, defaults to false)
        elif opt == '-v':
            verbosity = True
        elif opt in ("-i", "--ifile"):
            inputfile = arg
            inputflag = True
    if inputflag:
        instance = SatInstance()
        instance.from_file(inputfile)
        #start_time = time.time()
        solve_dpll(instance, verbosity)
        #print("--- %s seconds ---" % (time.time() - start_time))

    else:
        print("You must have an input file!")
        print('DPLLsat.py -i <inputCNFfile> [-v]')


# Finds a satisfying assignment to a SAT instance,
# using the DPLL algorithm.
# Input: a SAT instance and verbosity flag
# Output: print "UNSAT" or
#    "SAT"
#    list of true literals (if verbosity == True)
#
#  You will need to define your own
#  DPLLsat(), DPLL(), pure-elim(), propagate-units(), and
#  any other auxiliary functions
def solve_dpll(instance, verbosity):
    # print(instance)
    # instance.VARS goes 1 to N in a dict
    # print(instance.VARS)
    # print(instance.clauses)
    # print(verbosity)
    ###########################################
    # Start your code
    clauses = instance.clauses
    variables = instance.VARS
    model = []

    ret = DPLL(clauses, variables, model, "empty")
    if ret != "Fail":
        if(verbosity):
            print("SAT" + str(getSolution(ret)))
        else:
            print("SAT")
    else:
        print("UNSAT")






    ###########################################

def DPLL(clauses, variables, model, modelAdd):
    newModel = model[:]
    newVariables = variables[:]
    newClauses = clauses[:]
    
    if(modelAdd != "empty"):
        newModel.append(modelAdd)
    test = simplifyClauses(newClauses, newModel)
    if test == "emptyClause":
        return "Fail"
        
    if len(newClauses) == 0:
        return newModel
    #print(newClauses)
    #print(newModel)
    #print(newVariables)
    if(len(newVariables) == 0):
        for clause in newClauses:
            newClause = []
            for var in clause:
                for x in newModel:
                    if abs(var) == x[0]:
                        if(var < 0):
                            newClause.append(not x[1])
                            #print(newClause)
                        else:
                            newClause.append(x[1])
                            #print(newClause)
            if(evalClause(newClause) == False):
                return "Fail"
        return newModel
    
    test1 = pureElim(newClauses, newVariables, newModel)
    if test1 == "Success":
        return DPLL(newClauses, newVariables, newModel, "empty")
    
    
    test2 = propogateUnits(newClauses, newVariables, newModel)
    if test2 == "Success":
        return DPLL(newClauses, newVariables, newModel, "empty")
        
    P = newVariables.pop()
    
    
    modelAdd = [P, True]
    ret = DPLL(newClauses, newVariables, newModel, modelAdd)
    #print("1" + str(ret))
    if ret != "Fail":
        return ret
    modelAdd = [P, False]
    ret = DPLL(newClauses, newVariables, newModel, modelAdd)
    #print("2" + str(ret))
    if ret != "Fail":
        return ret
    return "Fail"

def evalClause(clause):
    falseCount = 0
    for var in clause:
        if(var == False):
            falseCount += 1

    if falseCount == len(clause):
        return False
    else:
        return True

def propogateUnits(clauses, variables, model):
    varChanged = False
    #print(model)
    #print(variables)
    for clause in clauses:
        if len(clause) == 1:
            isFound = False
            for var in model:
                if abs(clause[0]) == var[0]:
                    isFound = True
            if isFound == False:
                if clause[0] < 0:
                    model.append([abs(clause[0]), False])
                else:
                    model.append([clause[0], True])
                variables.remove(abs(clause[0]))
                varChanged = True
    if varChanged:
        return "Success"
    else:
        return "Failure"

def pureElim(clauses, variables, model):
    Success = "Failure"
    i = 0
    while i < len(variables):
        isPure = True
        first = True
        tempVar = variables[i]
        for clause in clauses:
            for x in clause:
                if abs(x) == variables[i]:
                    if first:
                        tempVar = x
                        first = False
                    else:
                        if tempVar != x:
                            isPure = False
                            break
            if isPure == False:
                break
        if isPure:
            if tempVar < 0:
                model.append([abs(tempVar), False])
            else:
                model.append([tempVar, True])
            variables.remove(abs(tempVar))
            Success = "Success"
            #print(model)
        else:
            i+= 1
    return Success
                

def simplifyClauses(clauses, model):
    newClauses = clauses

    #removes satisified clauses
    j = 0
    Success = False
    while j < len(newClauses):
        #print(j)
        #print(len(newClauses))
        for var in newClauses[j]:
            for x in model:
                if(abs(var) == x[0]):
                    #print(x)
                    if var < 0 and x[1] == False:
                        #print("-!" + str(len(newClauses)))
                        del newClauses[j]
                        Success = True
                    elif var > 0 and x[1] == True:
                        #print("+!" + str(len(newClauses)))
                        del newClauses[j]
                        Success = True
            if Success:
                Success = False
                break
        j+= 1
    
    #removes unnecessary literals
    for i in range(len(newClauses)):
        for var in newClauses[i]:
            for x in model:
                if abs(var) == x[0]:
                    if var < 0 and x[1] == True:
                        tempClause = copy.copy(newClauses[i])
                        tempClause.remove(var)
                        newClauses[i] = tempClause
                    elif var > 0 and x[1] == False:
                        tempClause = copy.copy(newClauses[i])
                        tempClause.remove(var)
                        newClauses[i] = tempClause
                    if len(newClauses[i]) == 0:
                        return "emptyClause"
    return "Success" 

def getSolution(model):
    Solution = []
    for x in model:
        if x[1]:
            Solution.append(x[0])
    Solution.sort()
    return Solution
        
                


if __name__ == "__main__":
    main(sys.argv[1:])
