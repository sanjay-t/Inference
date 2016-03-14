import inferParam as param
import inferUtil as util
import copy

class Predicate:
    id = 1
    def __init__(self):
        self.name = ''
        self.pid = Predicate.id
        Predicate.id = Predicate.id + 1
        self.type = None
        self.argsList = None
        self.argsCount = None
        self.premiseObjs = []
        self.premiseCount = 0

    def printPredicate(self):
        i = 1
        pre_str = ''
        for pobj in self.premiseObjs:
            pre_str = pre_str + pobj.printPredicate()
        if self.type == param.PREDICATE_TYPE['CC']:
            pre_str += '=>'
        pre_str += self.name + '('
        args_num = len(self.argsList)
        for i in range(args_num):
            if i < args_num-1:
                if(self.argsList[i].islower()):
                    pre_str += '_, '
                else:
                    pre_str += str(self.argsList[i])+', '
            else:
                if(self.argsList[i].islower()):
                    pre_str += '_'
                else:
                    pre_str += str(self.argsList[i])
        pre_str += ')'
        return pre_str

final_write = ''
class Query:
    def __init__(self, rule):
        self.pobj = util.get_pred_object(rule, param.PREDICATE_TYPE['QUERY'])

    def infer(self):
        global final_write
        outputFile = open("outputFile.txt","w")
        theta = {}
        theta['_status'] = param.VALID_RULE
        theta_list = FOL_BC_OR(self.pobj, theta, {})
        if theta_list==[]:
            print "False:", self.pobj.printPredicate()
            final_write += "False:"+self.pobj.printPredicate()+'\n'
        else:
            temp = Substitute(self.pobj, theta_list[0])
            final_write += "True: "+self.pobj.printPredicate()+'\n'
            print "True:", temp.printPredicate()
        result = param.INVALID_RULE
        for t in theta_list:
            if t['_status'] == param.VALID_RULE:
                final_write += 'True'
                for x in final_write:
                    outputFile.write(x)
                print "\n\n\nFWRITEE\n",final_write
                return 'TRUE\n'
        final_write += 'False'
        for x in final_write:
            outputFile.write(x)
        print "FWRITEE",final_write
        return 'FALSE\n'


def FOL_BC_OR(pobj, theta, ruleids):
    global final_write
    flag = 0;
    ruleList = Search_Rule(pobj.name, pobj.argsCount)
    returnList = []
    print "ASK:", pobj.printPredicate()
    final_write += "Ask: "+pobj.printPredicate()+'\n'
    for rule in ruleList:
        if flag:
            flag = 0
        inner_theta = copy.deepcopy(theta)
        inner_ruleids = copy.deepcopy(ruleids)
        arg_goal = str(pobj.argsList)
        if rule.pid in inner_ruleids:
            if arg_goal in inner_ruleids[rule.pid]:
                continue
            else:
                inner_ruleids[rule.pid].append(arg_goal)
        else:
            inner_ruleids[rule.pid] = [arg_goal]
        rule, inner_theta = Standardize(rule, inner_theta)
        temp_theta = Unify(rule.argsList, pobj.argsList, inner_theta)
        returnList.extend(FOL_BC_AND(rule.premiseObjs, temp_theta, inner_ruleids))
        if len(returnList) == 0:
            flag = 1
    return returnList


def FOL_BC_AND(goals, theta, ruleids):
    global final_write
    if theta['_status'] == param.INVALID_RULE:
        return []
    elif len(goals) == 0:
        return [theta]
    first, rest = goals[0], goals[1:]
    first = Substitute(first, theta)
    theta_d = FOL_BC_OR(first, theta, ruleids)
    if theta_d == []:
        print "False: ", first.printPredicate()
        final_write += "False: "+first.printPredicate()+'\n'
    else:
        temp = Substitute(first, theta_d[0])
        print "True: ", temp.printPredicate()
        final_write += "True: "+temp.printPredicate()+'\n'
    resultList = []
    for t in theta_d:
        resultList.extend(FOL_BC_AND(rest, t, ruleids))
    return resultList


def Substitute(pobj, theta):
    pobj_c = util.Clone_pobj(pobj)
    for i in range(len(pobj_c.argsList)):
        if pobj_c.argsList[i][0].islower() and theta[pobj_c.argsList[i]]:
            pobj_c.argsList[i] = theta[pobj_c.argsList[i]]
    return pobj_c


def Unify(rhs, goal, theta):
    print "TTTTTTTTTTT",theta
    print rhs, goal
    if theta['_status'] == param.INVALID_RULE:
        return theta
    elif len(goal) == 1:
        if rhs[0] == goal[0]:
            return theta
        elif rhs[0][0].islower():  # rhs[0] is variable case 1
            return Unify_Var(rhs[0], goal[0], theta)
        elif goal[0][0].islower():  # goal[0] is variable and rhs[0] is constant case 2
            return Unify_Var(goal[0], rhs[0], theta)
        else:
            theta['_status'] = param.INVALID_RULE
            return theta
    else:
        t = Unify([rhs[0]], [goal[0]], theta)
        return Unify(rhs[1:], goal[1:], t)


def Unify_Var(var, prob_const, theta):
    '''
        in case 1: prob_const can be variable or constant
        in case 2: prob_const is always constant
    '''
    if (var in theta.keys()) and theta[var]:
        return Unify([theta[var]], [prob_const], theta)
    elif (prob_const in theta.keys()) and theta[prob_const]:
        return Unify([var], [theta[prob_const]], theta)
    else:
        theta[var] = prob_const
        return theta


def Standardize(pobj, theta):
    if pobj.type == param.PREDICATE_TYPE['FACT']:
        return pobj, theta
    else:
        replaceMap = {}
        addMap = []
        pobj_c = util.Clone_pobj(pobj)
        chkList = [pobj_c]
        for elem in pobj_c.premiseObjs:
            chkList.append(elem)
        for elem in chkList:
            for i in range(elem.argsCount):
                if elem.argsList[i][0].isupper():
                    continue
                origvar = elem.argsList[i]
                var = origvar
                if origvar in theta:
                    unique = False
                    while not unique:
                        var = util.get_new_name(var)
                        unique = var not in theta
                    elem.argsList[i] = var
                    if not var in addMap:
                        addMap.append(var)
                else:
                    addMap.append(origvar)
        for newv in addMap:
            theta[newv] = None
        return pobj_c, theta


def Search_Rule(name, argCount):
    ruleList = []
    ruleList.extend(util.get_kb_list(param.PREDICATE_TYPE['FACT'], name, argCount))
    ruleList.extend(util.get_kb_list(param.PREDICATE_TYPE['CC'], name, argCount))
    return ruleList
