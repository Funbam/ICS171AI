#include"BTSolver.hpp"

using namespace std;

// =====================================================================
// Constructors
// =====================================================================

BTSolver::BTSolver ( SudokuBoard input, Trail* _trail,  string val_sh, string var_sh, string cc )
: sudokuGrid( input.get_p(), input.get_q(), input.get_board() ), network( input )
{
	valHeuristics = val_sh;
	varHeuristics = var_sh; 
	cChecks =  cc;

	trail = _trail;
}

// =====================================================================
// Consistency Checks
// =====================================================================

// Basic consistency check, no propagation done
bool BTSolver::assignmentsCheck ( void )
{
	for ( Constraint c : network.getConstraints() )
		if ( ! c.isConsistent() )
			return false;

	return true;
}

// =================================================================
// Arc Consistency
// =================================================================
bool BTSolver::arcConsistency ( void )
{
    vector<Variable*> toAssign;
    vector<Constraint*> RMC = network.getModifiedConstraints();
    for (int i = 0; i < RMC.size(); ++i)
    {
        vector<Variable*> LV = RMC[i]->vars;
        for (int j = 0; j < LV.size(); ++j)
        {
            if(LV[j]->isAssigned())
            {
                vector<Variable*> Neighbors = network.getNeighborsOfVariable(LV[j]);
                int assignedValue = LV[j]->getAssignment();
                for (int k = 0; k < Neighbors.size(); ++k)
                {
                    Domain D = Neighbors[k]->getDomain();
                    if(D.contains(assignedValue))
                    {
                        if (D.size() == 1)
                            return false;
                        if (D.size() == 2)
                            toAssign.push_back(Neighbors[k]);
                        trail->push(Neighbors[k]);
                        Neighbors[k]->removeValueFromDomain(assignedValue);
                    }
                }
            }
        }
    }
    if (!toAssign.empty())
    {
        for (int i = 0; i < toAssign.size(); ++i)
        {
            Domain D = toAssign[i]->getDomain();
            vector<int> assign = D.getValues();
            trail->push(toAssign[i]);
            toAssign[i]->assignValue(assign[0]);
        }
        return arcConsistency();
    }
    return network.isConsistent();
}

/**
 * Part 1 TODO: Implement the Forward Checking Heuristic
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all MODIFIED variables, mapped to their MODIFIED domain. 
 * 		   The bool is true if assignment is consistent, false otherwise.
 */
pair<map<Variable*,Domain>,bool> BTSolver::forwardChecking ( void )
{
	
	ConstraintNetwork::ConstraintRefSet constraints = network.getModifiedConstraints();
	for(Constraint * constraint : constraints){
		for(Variable * var : constraint->vars){
			if(var->isAssigned()){
				for(Variable * neighbor : network.getNeighborsOfVariable(var)){
					int assignedValue = var->getAssignment();
					Domain D = neighbor->getDomain();
                    if(D.contains(assignedValue))
                    {
                        if (D.size() == 1)
                            return make_pair(map<Variable*, Domain>(), false);
                        trail->push(neighbor);
                        neighbor->removeValueFromDomain(assignedValue);
                    }
				}
			}
		}
	}
	return make_pair(map<Variable*, Domain>(), assignmentsCheck());
	
}

/**
 * Part 2 TODO: Implement both of Norvig's Heuristics
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * (2) If a constraint has only one possible place for a value
 *     then put the value there.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all variables that were assigned during 
 *         the whole NorvigCheck propagation, and mapped to the values that they were assigned. 
 *         The bool is true if assignment is consistent, false otherwise.
 */
pair<map<Variable*,int>,bool> BTSolver::norvigCheck ( void )
{
 
	if (!forwardChecking().second) return make_pair(map<Variable*, int>(), false);

	// if (!assignmentsCheck())
	// 	return make_pair(map<Variable*, int>(), false);

	ConstraintNetwork::ConstraintRefSet all_constraints = network.getModifiedConstraints();
    // ConstraintNetwork::ConstraintSet all_constraints = network.getConstraints();
    // for(Constraint constraint : all_constraints){
    //     for (int i = 1; i <= sudokuGrid.get_n(); i++){
    //         int pos_count = 0;
    //         Variable * singleSlot = nullptr;
    //         for(Variable * var : constraint.vars){
    //             if(var->getDomain().contains(i)){
    //                 pos_count++;
	// 				if (pos_count > 1) 
	// 					break;
    //                 singleSlot = var;
    //             }

    //         }
    //         if (pos_count == 1){
    //             trail->push(singleSlot);
    //             singleSlot->assignValue(i);
    //         }
    //         if(pos_count == 0){
    //             return make_pair(map<Variable*, int>(), false);
    //         }
    //     }
    // }

	for(Constraint* constraint : all_constraints)
	{
		int counter [sudokuGrid.get_n()] = {0};
		for(int i = 0; i < sudokuGrid.get_n(); ++i)
		{
			for(int value : constraint -> vars[i]->getValues())
			{
				counter[value - 1] += 1;
			}

		}

		for(int i = 0; i < sudokuGrid.get_n(); ++i)
		{
			if (counter[i] == 1)
			{
				for(Variable* var : constraint -> vars)
				{
					if (!(var ->isAssigned()) && var -> getDomain().contains(i + 1))
					{
						trail->push(var);
						var->assignValue(i + 1);
						// for (Constraint* c : network.getModifiedConstraints())
						// {	
						// 	if (!(c->isConsistent()))
						// 		return make_pair(map<Variable*, int>(), false);
						// }
					}

				}

			}
		}

	}

	return make_pair(map<Variable*, int>(), assignmentsCheck());
}

/**
 * Optional TODO: Implement your own advanced Constraint Propagation
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
bool BTSolver::getTournCC ( void )
{
	return false;
}

// =====================================================================
// Variable Selectors
// =====================================================================

// Basic variable selector, returns first unassigned variable
Variable* BTSolver::getfirstUnassignedVariable ( void )
{
	for ( Variable* v : network.getVariables() )
		if ( !(v->isAssigned()) )
			return v;

	// Everything is assigned
	return nullptr;
}

/**
 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
 *
 * Return: The unassigned variable with the smallest domain
 */
Variable* BTSolver::getMRV ( void )
{
	vector<Variable*> list = network.getVariables();
	Variable* var = nullptr;
	for(Variable* variable : list){
		if(!(variable->isAssigned())){
			if(var == nullptr){
				var = variable;
			}
			else if (variable->getDomain().size() < var->getDomain().size())
			{
				var = variable;
			}
			
		}
	}
	
    return var;
}

/**
 * Part 2 TODO: Implement the Minimum Remaining Value Heuristic
 *                with Degree Heuristic as a Tie Breaker
 *
 * Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
 * 		   If there are multiple variables that have the same smallest domain with the same number 
 * 		   of unassigned neighbors, add them to the vector of Variables.
 *         If there is only one variable, return the vector of size 1 containing that variable.
 */
vector<Variable*> BTSolver::MRVwithTieBreaker ( void )
{
	vector<Variable*> list;
	vector<Variable*> variables = network.getVariables();
	for(Variable* variable : variables){
		if(!(variable->isAssigned())){
			if(list.empty()){
				list.push_back(variable);
			}
			else if (variable->getDomain().size() < list[0]->getDomain().size())
			{
				list.clear();
				list.push_back(variable);

			}
			else if(variable->getDomain().size() == list[0]->getDomain().size()){
				list.push_back(variable);
			}
			
		}
	}

	vector<Variable*> final_list;

	int currentBest = -1;
	for (Variable* variable : list) {
    	int numUnassignedNeighbors = 0;
		for (Variable* neighbor : network.getNeighborsOfVariable(variable)) {
			if (!(neighbor->isAssigned())) {
				numUnassignedNeighbors++;
			}
		}

		if (numUnassignedNeighbors > currentBest) {
			final_list.clear();
			currentBest = numUnassignedNeighbors;
			final_list.push_back(variable);
		} else if (numUnassignedNeighbors == currentBest) {
			final_list.push_back(variable);
    	}
	}

	if (final_list.empty())
	{
		Variable* tmp = nullptr;
		final_list.push_back(tmp);
	}


	//At this point, list contains all variables with MRV. These now need to be tiebroken with LCV

    return final_list;
}

/**
 * Optional TODO: Implement your own advanced Variable Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
Variable* BTSolver::getTournVar ( void )
{
	return nullptr;
}

// =====================================================================
// Value Selectors
// =====================================================================

// Default Value Ordering
vector<int> BTSolver::getValuesInOrder ( Variable* v )
{
	vector<int> values = v->getDomain().getValues();
	sort( values.begin(), values.end() );
	return values;
}

/**
 * Part 1 TODO: Implement the Least Constraining Value Heuristic
 *
 * The Least constraining value is the one that will knock the least
 * values out of it's neighbors domain.
 *
 * Return: A list of v's domain sorted by the LCV heuristic
 *         The LCV is first and the MCV is last
 */

struct LCVStruct{
	int value;
	int LCVcount;

	LCVStruct(int v, int c): value(v), LCVcount(c){}

	bool operator < (const LCVStruct& str) const
    {
        return (LCVcount < str.LCVcount);
    }

};

vector<int> BTSolver::getValuesLCVOrder ( Variable* v )
{
	vector<LCVStruct> lcvs;

	for(int value : v->getDomain()){
		int numConflicts = 0;
		for(Variable * neighbor : network.getNeighborsOfVariable(v)){
			if(!(neighbor->isAssigned()) && neighbor->getDomain().contains(value)){
				++numConflicts;
			}
		}
		lcvs.push_back(LCVStruct(value, numConflicts));
	}

	sort(lcvs.begin(), lcvs.end());


	vector<int> sortedVector;
	for(LCVStruct s : lcvs){
		sortedVector.push_back(s.value);
	}

    return sortedVector;
}

/**
 * Optional TODO: Implement your own advanced Value Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
vector<int> BTSolver::getTournVal ( Variable* v )
{
	return vector<int>();
}

// =====================================================================
// Engine Functions
// =====================================================================

int BTSolver::solve ( float time_left)
{
	if (time_left <= 60.0)
		return -1;
	double elapsed_time = 0.0;
    clock_t begin_clock = clock();

	if ( hasSolution )
		return 0;

	// Variable Selection
	Variable* v = selectNextVariable();

	if ( v == nullptr )
	{
		for ( Variable* var : network.getVariables() )
		{
			// If all variables haven't been assigned
			if ( ! ( var->isAssigned() ) )
			{
				return 0;
			}
		}

		// Success
		hasSolution = true;
		return 0;
	}

	// Attempt to assign a value
	for ( int i : getNextValues( v ) )
	{
		// Store place in trail and push variable's state on trail
		trail->placeTrailMarker();
		trail->push( v );
		// Assign the value
		v->assignValue( i );
		//lastModified.push_back(v);

		// Propagate constraints, check consistency, recurse
		if ( checkConsistency() ) {
			clock_t end_clock = clock();
			elapsed_time += (float)(end_clock - begin_clock)/ CLOCKS_PER_SEC;
			double new_start_time = time_left - elapsed_time;
			int check_status = solve(new_start_time);
			if(check_status == -1) {
			    return -1;
			}
			
		}

		// If this assignment succeeded, return
		if ( hasSolution )
			return 0;

		// Otherwise backtrack
		trail->undo();
	}
	return 0;
}

bool BTSolver::checkConsistency ( void )
{
	if ( cChecks == "forwardChecking" )
		return forwardChecking().second;

	if ( cChecks == "norvigCheck" )
		return norvigCheck().second;

	if ( cChecks == "tournCC" )
		return getTournCC();
	return assignmentsCheck();
}

Variable* BTSolver::selectNextVariable ( void )
{
	if ( varHeuristics == "MinimumRemainingValue" )
		return getMRV();

	if ( varHeuristics == "MRVwithTieBreaker" )
		return MRVwithTieBreaker()[0];

	if ( varHeuristics == "tournVar" )
		return getTournVar();

	return getfirstUnassignedVariable();
}

vector<int> BTSolver::getNextValues ( Variable* v )
{
	if ( valHeuristics == "LeastConstrainingValue" )
		return getValuesLCVOrder( v );

	if ( valHeuristics == "tournVal" )
		return getTournVal( v );

	return getValuesInOrder( v );
}

bool BTSolver::haveSolution ( void )
{
	return hasSolution;
}

SudokuBoard BTSolver::getSolution ( void )
{
	return network.toSudokuBoard ( sudokuGrid.get_p(), sudokuGrid.get_q() );
}

ConstraintNetwork BTSolver::getNetwork ( void )
{
	return network;
}
