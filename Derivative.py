 
### method from Derivative class
### derarr is the array in which all the expr are stored recursively to complile later on

def __new__(cls, expr, *variables, **assumptions):
        
	
	global numderiv
	global derarr
	derarr.append(expr)
	
        expr = sympify(expr)
        # There are no variables, we differentiate wrt all of the free symbols
        # in expr.
        if not variables:
            variables = expr.free_symbols
            if len(variables) != 1:
                from sympy.utilities.misc import filldedent
                raise ValueError(filldedent('''
                    Since there is more than one variable in the
                    expression, the variable(s) of differentiation
                    must be supplied to differentiate %s''' % expr))

        # Standardize the variables by sympifying them and making appending a
        # count of 1 if there is only one variable: diff(e,x)->diff(e,x,1).
        variables = list(sympify(variables))
        if not variables[-1].is_Integer or len(variables) == 1:
            variables.append(S.One)

        # Split the list of variables into a list of the variables we are diff
        # wrt, where each element of the list has the form (s, count) where
        # s is the entity to diff wrt and count is the order of the
        # derivative.
        variable_count = []
        all_zero = True
        i = 0
        
        while i < len(variables) - 1:  # process up to final Integer
            v, count = variables[i: i + 2]
            iwas = i
            if v._diff_wrt:
                # We need to test the more specific case of count being an
                # Integer first.
                if count.is_Integer:
                    count = int(count)
                    i += 2
                elif count._diff_wrt:
                    count = 1
                    i += 1
	    """
            if i == iwas:  # didn't get an update because of bad input
                from sympy.utilities.misc import filldedent
                raise ValueError(filldedent('''
                Can\'t differentiate wrt the variable: %s, %s''' % (v, count)))
	    """
            if all_zero and not count == 0:
                all_zero = False

            if count:
                variable_count.append((v, count))

        # We make a special case for 0th derivative, because there is no
        # good way to unambiguously print this.
        if all_zero:
            return expr

        # Pop evaluate because it is not really an assumption and we will need
        # to track it carefully below.
        evaluate = assumptions.pop('evaluate', False)

        # Look for a quick exit if there are symbols that don't appear in
        # expression at all. Note, this cannnot check non-symbols like
        # functions and Derivatives as those can be created by intermediate
        # derivatives.
        if evaluate:
            symbol_set = set(sc[0] for sc in variable_count if sc[0].is_Symbol)
            if symbol_set.difference(expr.free_symbols):
                return S.Zero

        # We make a generator so as to only generate a variable when necessary.
        # If a high order of derivative is requested and the expr becomes 0
        # after a few differentiations, then we won't need the other variables.
        variablegen = (v for v, count in variable_count for i in xrange(count))

        # If we can't compute the derivative of expr (but we wanted to) and
        # expr is itself not a Derivative, finish building an unevaluated
        # derivative class by calling Expr.__new__.
        if (not (hasattr(expr, '_eval_derivative') and evaluate) and
           (not isinstance(expr, Derivative))):
            variables = list(variablegen)
            # If we wanted to evaluate, we sort the variables into standard
            # order for later comparisons. This is too aggressive if evaluate
            # is False, so we don't do it in that case.
            if evaluate:
                #TODO: check if assumption of discontinuous derivatives exist
                variables = cls._sort_variables(variables)
            # Here we *don't* need to reinject evaluate into assumptions
            # because we are done with it and it is not an assumption that
            # Expr knows about.
	   
            obj = Expr.__new__(cls, expr, *variables, **assumptions)
	    #print("O",obj)
            return obj

        # Compute the derivative now by repeatedly calling the
        # _eval_derivative method of expr for each variable. When this method
        # returns None, the derivative couldn't be computed wrt that variable
        # and we save the variable for later.
        unhandled_variables = []

        # Once we encouter a non_symbol that is unhandled, we stop taking
        # derivatives entirely. This is because derivatives wrt functions
        # don't commute with derivatives wrt symbols and we can't safely
        # continue.
        unhandled_non_symbol = False
        nderivs = 0  # how many derivatives were performed
	#print("varibale",variablegen)
        for v in variablegen:
            is_symbol = v.is_Symbol
	   

            if unhandled_non_symbol:
                obj = None
            else:
                if not is_symbol:
                    new_v = C.Dummy('xi_%i' % i)
                    new_v.dummy_index = hash(v)
                    expr = expr.subs(v, new_v)   
                    old_v = v
                    v = new_v
						
		numderiv+=1
		obj = expr._eval_derivative(v)
		numderiv-=1
				
                nderivs += 1
                if not is_symbol:
                    if obj is not None:
			#print("first",obj)
                        obj = obj.subs(v, old_v)
			#print("second",obj)
		    #print("v ",v,"old ",old_v)
                    v = old_v
	    #print("----expr is",obj)
            if obj is None:
		#print ("yeyyyyy")
                unhandled_variables.append(v)
                if not is_symbol:
                    unhandled_non_symbol = True
            elif obj is S.Zero:
                return S.Zero
            else:
                expr = obj
	#print("---expr is",expr.args[0:])
        if unhandled_variables:
            unhandled_variables = cls._sort_variables(unhandled_variables)
	    #print("1",expr)
            expr = Expr.__new__(cls, expr, *unhandled_variables, **assumptions)
        else:
            # We got a Derivative at the end of it all, and we rebuild it by
            # sorting its variables.
	    #print(isinstance(expr,Derivative))
            if isinstance(expr, Derivative):
		#print("#",expr.args[0])
                expr = cls(
                    expr.args[0], *cls._sort_variables(expr.args[1:])
                )
		#print("##",expr)
	    #print("--expr is",expr)
	#print("-expr is",expr)
        if nderivs > 1 and assumptions.get('simplify', True):
            from sympy.core.exprtools import factor_terms
            from sympy.simplify.simplify import signsimp
            expr = factor_terms(signsimp(expr))
	#print("expr is",expr)
	
	if numderiv==0:			# no of recursive derivatives
		from sympy.printing.pretty import pprint
		temparr = derarr	# so that following derivative does not causes infinite loop because it will keep adding to derarr.
		derarr=[]		# prevents infinite loop
		for i in temparr:
			pprint(Derivative(i,'x',evaluate=False))		
		derarr = []		# empties, so that next derivative expr find it empty..
	        
	return expr


########################################################
##### Multiplication
########################################################
def _eval_derivative(self, s):
	
	terms = list(self.args)
	
        factors = []
        for i in xrange(len(terms)):
            t = terms[i].diff(s)
            if t is S.Zero:
                continue
            factors.append(self.func(*(terms[:i] + [terms[i].diff(s,evaluate=False)] + terms[i + 1:])))
	
	from sympy.printing.pretty import pprint
	pprint(Add(*factors))


