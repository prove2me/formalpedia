-- Prove2me | Definitions.Def_Nintendo_sat
-- name    : Nintendo_sat
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T05:50:46.493281+00:00
-- url     : https://prove2.me/theorems/b077316b-fe68-4b74-9a6b-b8a9a1480e5e
-- title:
--   The logic layer: 3-CNF satisfiability and quantified Boolean truth
-- statement:
--   The logic layer of Aloupis, Demaine, Guo, and Viglietta's "Classic Nintendo games are (computationally) hard" (Theoretical Computer Science 586 (2015) 135-160): the propositional content of the paper's two frameworks. A literal is a variable index, optionally negated; a clause is a list of literals and a formula a list of clauses; a formula is 3-CNF when every clause has between one and three literals, and satisfiable when some assignment of the variables satisfies every clause. A quantified formula pairs a prefix of existential and universal quantifiers with a 3-CNF matrix. The truth definition reads the prefix outermost first: the innermost (rightmost) quantifier binds variable 0, and in general variable k is bound by the k-th quantifier counted from the right; a quantified formula is true when the recursive evaluation of the prefix over the matrix holds, the variables beyond the prefix evaluating to falsehood. The layer also carries the two size measures - the number of clauses plus the total number of literals for formulas, plus the prefix length for quantified formulas - to which the hardness statements' quadratic size bounds refer.
-- source:
--   G. Aloupis, E. D. Demaine, A. Guo, G. Viglietta, Classic Nintendo games are (computationally) hard, Theoret. Comput. Sci. 586 (2015) 135-160, Section 2 (after Cook 1971 and Stockmeyer and Meyer 1973).

import Mathlib

/-!
# The logic layer: 3-CNF satisfiability and quantified Boolean truth

The logic layer of the Nintendo mission: Boolean literals over natural-number
variables, clauses and 3-CNF formulas, satisfiability, quantifier prefixes,
and the truth of a quantified Boolean formula. The encoding carries the
propositional content of Section 2 of Aloupis, Demaine, Guo, and Viglietta,
"Classic Nintendo games are (computationally) hard", Theoretical Computer
Science 586 (2015) 135-160.
-/

namespace Nintendo

/-- A Boolean literal: a variable index, optionally negated. -/
inductive Lit where
  | pos (v : ℕ) : Lit
  | neg (v : ℕ) : Lit
  deriving Repr

/-- The variable index of a literal. -/
def litVar : Lit → ℕ
  | Lit.pos v => v
  | Lit.neg v => v

/-- The value of a literal under an assignment. -/
def evalLit (a : ℕ → Bool) : Lit → Bool
  | Lit.pos v => a v
  | Lit.neg v => !a v

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit

/-- A formula is a conjunction of clauses. -/
abbrev Form := List Clause

/-- A clause is satisfied when some literal is. -/
def evalClause (a : ℕ → Bool) (c : Clause) : Bool := c.any (evalLit a)

/-- A formula is satisfied when every clause is. -/
def evalForm (a : ℕ → Bool) (f : Form) : Bool := f.all (evalClause a)

/-- 3-CNF: every clause has between one and three literals. -/
def Is3Sat (f : Form) : Prop := ∀ c ∈ f, 1 ≤ c.length ∧ c.length ≤ 3

/-- A formula is satisfiable when some assignment satisfies it. -/
def Sat (f : Form) : Prop := ∃ a : ℕ → Bool, evalForm a f = true

/-- A size measure: the number of clauses plus the total number of literals. -/
def formulaSize (f : Form) : ℕ :=
  f.length + (f.map (fun c => c.length)).foldl (fun x y => x + y) 0

/-- A quantifier. -/
inductive Quant where
  | ex : Quant
  | univ : Quant
  deriving Repr

/-- A quantified formula: a prefix of quantifiers applied to a matrix. -/
abbrev QForm := List Quant × Form

/-- The truth of a quantified formula. The prefix is read outermost first:
the innermost (rightmost) quantifier binds variable 0, and in general
variable k is bound by the k-th quantifier counted from the right. The
threaded assignment carries the values already chosen for the quantified
variables; the variables beyond the prefix evaluate against the seed. -/
def qtrue : List Quant → Form → (ℕ → Bool) → Bool
  | [], f, a => evalForm a f
  | Quant.ex :: qs, f, a =>
      qtrue qs f (fun j => if j = 0 then true else a (j - 1)) ||
        qtrue qs f (fun j => if j = 0 then false else a (j - 1))
  | Quant.univ :: qs, f, a =>
      qtrue qs f (fun j => if j = 0 then true else a (j - 1)) &&
        qtrue qs f (fun j => if j = 0 then false else a (j - 1))

/-- A quantified formula is true. -/
def QTrue (ψ : QForm) : Prop := qtrue ψ.1 ψ.2 (fun _ => false) = true

/-- A quantified formula is a QBF when its matrix is 3-CNF. -/
def IsQbf (ψ : QForm) : Prop := Is3Sat ψ.2

/-- A size measure for quantified formulas: matrix size plus prefix length. -/
def qbfSize (ψ : QForm) : ℕ := formulaSize ψ.2 + ψ.1.length

end Nintendo


