import read


class Statement(object):
    def __init__(self, pattern):
        self.full = pattern
        self.predicate = pattern[0].upper()
        self.args = pattern[1:]
        self.facts = []
        self.rules = []

    def pretty(self):
        return "(" + ' '.join(self.full) + ")"

    def add_fact(self, fact1):
        self.facts.append(fact1)

    def add_rule(self, rule):
        self.rules.append(rule)


class Rule(object):
    count = 0

    def __init__(self, lhs, rhs):
        self.full = lhs + rhs
        self.type = "Assert"
        self.name = "Rule " + str(Rule.count)
        self.lhs = map(lambda (x): Statement(x), lhs)
        if rhs[0][0] == "~":
            rhs[0] = rhs[0][1:]
            self.type = "Retract"
        self.rhs = Statement(rhs)
        self.facts = []
        self.rules = []
        Rule.count = Rule.count + 1

    def pretty(self):
        return str(self.name) + ": When <" + " ".join(map(lambda x: x.pretty(), self.lhs)) + "> " + str(
            self.type) + " " + str(self.rhs.pretty())

    def add_fact(self, fact2):
        self.facts.append(fact2)

    def add_rule(self, rule):
        self.rules.append(rule)


def match(pattern, fact3):
    p = pattern.full
    f = fact3.full
    if p[0] != f[0]:
        return False
    return match_args(p[1:], f[1:])


def match_args(pattern_args, fact_args):
    bindings = {}
    # print(pattern_args, fact_args)
    for p, f in zip(pattern_args, fact_args):
        bindings = match_element(p, f, bindings)
        if not bindings:
            return False
    return bindings


def match_element(p, f, bindings):
    # print(p, f, bindings)
    if p == f:
        return bindings
    elif var(p):
        bound = bindings.get(p, False)
        if bound:
            if f == bound:
                return bindings
            else:
                return False
        else:
            bindings[p] = f
            return bindings
    else:
        return False


def instantiate(pattern, bindings):
    predicate = pattern[0]
    args = map(lambda x: bindings.get(x, x), pattern[1:])
    args.insert(0, predicate)
    return args


def var(item):
    if item[0] == "?":
        return True
    else:
        return False


#############################knowledge base###############################


def assert_fact(fact4):
    temp_kb = []
    for f in KB:
        temp_kb.append(f.full)
    if fact4.full not in temp_kb:
        KB.append(fact4)
        infer_from_fact(fact4)


def assert_rule(rule):
    temp_rb = []
    for r in RB:
        temp_rb.append(r.full)
    if rule.full not in temp_rb:
        RB.append(rule)
        infer_from_rule(rule)


def infer_from_fact(fact5):
    for r in RB:
        bindings = match(r.lhs[0], fact5)
        if bindings:
            if r.type == "Assert":
                if len(r.lhs) == 1:
                    new_statement = Statement(instantiate(r.rhs.full, bindings))
                    fact5.add_fact(new_statement)
                    r.add_rule(new_statement)
                    assert_fact(new_statement)
                else:
                    tests = map(lambda x: instantiate(x.full, bindings), r.lhs[1:])
                    rhs = instantiate(r.rhs.full, bindings)
                    new_rule = Rule(tests, rhs)
                    r.add_rule(new_rule)
                    fact5.add_rule(new_rule)
                    assert_rule(new_rule)
            if r.type == "Retract":
                new_statement = Statement(instantiate(r.rhs.full, bindings))
                fact5.add_fact(new_statement)
                for ff in fact5.facts:
                    delete(ff)
                for rr in fact5.rules:
                    delete(rr)


def infer_from_rule(rule):
    for f in KB:
        bindings = match(rule.lhs[0], f)
        if bindings:
            if rule.type == "Assert":
                if len(rule.lhs) == 1:
                    new_statement = Statement(instantiate(rule.rhs.full, bindings))
                    rule.add_fact(new_statement)
                    f.add_fact(new_statement)
                    assert_fact(new_statement)
                else:
                    tests = map(lambda x: instantiate(x.full, bindings), rule.lhs[1:])
                    rhs = instantiate(rule.rhs.full, bindings)
                    new_rule = Rule(tests, rhs)
                    rule.add_rule(new_rule)
                    f.add_rule(new_rule)
                    assert_rule(new_rule)

            if rule.type == "Retract":
                new_statement = Statement(instantiate(rule.rhs.full, bindings))
                f.add_fact(new_statement)
                for ff in f.facts:
                    delete(ff)
                for rr in f.rules:
                    delete(rr)


def delete(factorrule):
    temp = []
    for fact_temp in KB:
        if factorrule.full == fact_temp.full:
            print 'delete the fact: ' + fact_temp.pretty()
            temp.append(fact_temp)
            KB.remove(fact_temp)
    for rule_temp in RB:
        if rule_temp.full == factorrule.full:
            print 'delete the rule: ' + rule_temp.pretty()
            temp.append(rule_temp)
            RB.remove(rule_temp)

    for insf in temp:
        for s in insf.facts:
            print 'Relevant facts(support): ' + s.pretty()
            delete(s)
    for insr in temp:
        for s in insr.rules:
            print 'Relevant rules(support): ' + s.pretty()
            delete(s)
    return


def ask(pattern, flag):
    result = []
    list_of_bindings_lists = []
    for fact in KB:
        bindings = match(Statement(pattern), fact)
        if bindings and not (bindings in list_of_bindings_lists):
            list_of_bindings_lists.append(bindings)
            if flag == 1:
                print "Asking " + Statement(pattern).pretty()
                print "This is true: \t",
                print Statement(instantiate(pattern, bindings)).pretty()
            result.append(Statement(instantiate(pattern, bindings)))
    if len(list_of_bindings_lists) == 0:
        if flag == 1:
            print 'No matching solutions \n'
    return result


def retract(pattern):
    fact = Statement(pattern)
    delete(fact)


if __name__ == "__main__":
    global KB
    global RB
    KB = []
    RB = []

    facts, rules = read.read_tokenize("statements.txt")

    for fact in facts:
        assert_fact(Statement(fact))
    for new_rule in rules:
        assert_rule(Rule(new_rule[0], new_rule[1]))

    print '\n*******************************Knowledge Base*******************************************\n'
    for kb in KB:
        print "fact: " + kb.pretty()
    print '\n*******************************Rules Base*******************************************\n'
    for rb in RB:
        print rb.pretty()

    print '\n******************************* Ask *******************************************\n'
    result1 = ask(['color', 'pyramid1', '?x'], 1)
    ask(['size', 'littlebox', '?x'], 1)
    result3 = ask(['color', '?x', 'green'], 1)

    print '\n******************************* Retract *******************************************\n'
    retract(['isa', 'cube', 'block'])

    print '\n******************************* Knowledge Base After Retract *******************************************\n'
    for ele in KB:
        print ele.pretty()
