-- Prove2me | Definitions.Def_LiftSAParity_CNF
-- name    : LiftSAParity_CNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:29.32519+00:00
-- url     : https://prove2.me/theorems/bdd4ba71-f554-4bab-869d-9ccbcd852aca
-- title:
--   Clauses, CNF formulas and satisfiability
-- statement:
--   Let $V$ be a set of variables. A **literal** is a pair $(v,b)$ with $v\in V$ and $b\in\{0,1\}$: $(v,1)$ is the literal $x_v$ and $(v,0)$ is $\bar x_v=\neg x_v$. A **clause** $C$ is a finite set of literals, read as their disjunction, and a **CNF formula** $\varphi$ is a finite set of clauses, read as their conjunction.
--
--   An assignment $a\in\{0,1\}^V$ **falsifies** $C$ when every literal of $C$ is false, i.e. $a_v\neq b$ for every $(v,b)\in C$. The formula $\varphi$ is **satisfiable** when some assignment falsifies none of its clauses. The variables of $C$ are $\mathrm{vars}(C)=\{v:(v,b)\in C\}$.
--
--   These are the formulas the paper refutes: the unlifted formula $F$ on $n$ variables and the lifted formula $F\circ g$ on $n\cdot\ell$ variables.
--
--   **Formalization Note** A clause may contain a complementary pair (it is then satisfied by every assignment) and may be empty (it is then falsified by every assignment).
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §1.1, p.4; §3, p.8

import Mathlib

namespace LiftSAParity

/-- A clause over the variable set `V` (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams
Degree to Unary Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §3, p.8): a
finite set of literals. The literal `(v, true)` is `x_v` and `(v, false)` is `x̄_v = ¬x_v`.

**Formalization Note** A clause containing both `(v, true)` and `(v, false)` is allowed (it is
satisfied by every assignment). The empty clause is allowed (it is falsified by every assignment). -/
abbrev Clause (V : Type*) := Finset (V × Bool)

/-- A CNF formula over `V` (§1.1, p.4; §3, p.8): a finite set of clauses. -/
abbrev CNF (V : Type*) := Finset (Clause V)

/-- The assignment `a : V → Bool` falsifies the clause `C`: every literal of `C` is false under
`a`, i.e. `a v ≠ b` for every literal `(v, b) ∈ C`. -/
def Falsifies {V : Type*} (a : V → Bool) (C : Clause V) : Prop :=
  ∀ l ∈ C, a l.1 ≠ l.2

/-- The CNF formula `φ` is satisfiable: some assignment falsifies none of its clauses. -/
def Satisfiable {V : Type*} (φ : CNF V) : Prop :=
  ∃ a : V → Bool, ∀ C ∈ φ, ¬ Falsifies a C

/-- The set of variables occurring in the clause `C`. -/
def clauseVars {V : Type*} [DecidableEq V] (C : Clause V) : Finset V :=
  C.image Prod.fst

end LiftSAParity


