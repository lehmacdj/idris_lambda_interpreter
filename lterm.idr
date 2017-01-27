||| A variable is just a string
Variable : Type
Variable = String

||| Represents a term in the lambda calculus
data LTerm : Type where
  Var : Variable -> LTerm
  Lambda : Variable -> LTerm -> LTerm
  Application : LTerm -> LTerm -> LTerm

||| Substitutes a variable for all of its instances in scope in a lambda-term
substitute : Variable -> LTerm -> LTerm -> LTerm
substitute v (Var v') with_e =
  if v == v'
     then with_e
     else (Var v')
substitute v (Lambda v' in_e) with_e =
  if v == v'
     then Lambda v' in_e
     else Lambda v' (substitute v in_e with_e)
substitute v (Application e1 e2) with_e =
  Application (substitute v e1 with_e) (substitute v e2 with_e)

||| Evaluate a lambda expression
eval : LTerm -> LTerm
eval (Var v) = Var v
eval (Lambda v e) = Lambda v (eval e)
eval (Application (Lambda v e1) e2) = substitute v e1 e2
