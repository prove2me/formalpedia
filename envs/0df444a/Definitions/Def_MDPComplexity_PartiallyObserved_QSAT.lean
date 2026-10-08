-- Prove2me | Definitions.Def_MDPComplexity_PartiallyObserved_QSAT
-- name    : MDPComplexity_PartiallyObserved_QSAT
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:36:11.583985+00:00
-- url     : https://prove2.me/theorems/d7755949-dfaf-41f5-b4aa-3a31fce560db
-- title:
--   §2 (p. 443): quantified Boolean formulas in conjunctive normal form and their truth
-- statement:
--   A **quantified Boolean formula** (the input of quantified satisfiability, QSAT, p. 443) has the form
--   $$
--   Q_1 x_1\, Q_2 x_2 \cdots Q_n x_n\; F(x_1, \dots, x_n),
--   $$
--   where each $Q_j$ is $\exists$ or $\forall$ and $F = C_1 \wedge \dots \wedge C_m$ is in conjunctive normal form: each clause $C_i$ is a finite set of literals $x_j$ or $\neg x_j$, and $F$ is true under a truth assignment when every clause contains a true literal.
--
--   The formula is **true** if, going through the variables in order, the quantified condition holds: there exists a truth value for $x_1$ (if $Q_1 = \exists$) such that for all truth values of $x_2$ (if $Q_2 = \forall$), and so on up to $x_n$, the matrix $F$ comes out true. Formally, with $x$ the values already fixed, the condition from variable $k$ on is
--   $$
--   H_k(x) = \begin{cases} \exists b \in \{0,1\}:\ H_{k+1}(x[x_k := b]) & Q_k = \exists,\\ \forall b \in \{0,1\}:\ H_{k+1}(x[x_k := b]) & Q_k = \forall,\end{cases} \qquad H_{n+1}(x) = F(x),
--   $$
--   and the formula is true iff $H_1$ holds.
--
--   QSAT is the PSPACE-complete problem the paper reduces to the partially observed Markov decision problem.
--
--   **Formalization Note.** The general `QBF` structure allows any quantifier prefix (`q j = true` for $\exists$) and clauses of any width. `IsPaperQSAT` singles out the paper's alternating prefix $\exists x_1 \forall x_2 \cdots \forall x_n$ with $n>0$ even and three literals per clause; it is a hypothesis of every theorem item. Clauses are sets, so three witnesses permit repeated literals. Paper variable $x_j$ is Lean index $j-1$, paper clause $C_i$ is Lean index $i-1$; the literal $x_j$ is `(j, true)` and $\neg x_j$ is `(j, false)`. Truth is defined by recursion on the index of the next variable, starting from an arbitrary assignment (every variable is overwritten before $F$ is evaluated).
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 443, §2 Complexity (QSAT)

import Mathlib

namespace MDPComplexity.PartiallyObserved

/-- A quantified Boolean formula in prenex conjunctive normal form (p. 443): `n` variables
`x_1, …, x_n` (Lean index `j` is the paper's `x_{j+1}`), each quantified existentially
(`q j = true`) or universally (`q j = false`), and `m` clauses; clause `i` is a finite set of
literals, `(j, true)` standing for `x_j` and `(j, false)` for `¬x_j`. -/
structure QBF (n m : ℕ) where
  q : Fin n → Bool
  clause : Fin m → Finset (Fin n × Bool)

variable {n m : ℕ}

/-- The QSAT input specified on p. 443: a nonempty alternating prefix beginning with an
existential variable and ending with a universal variable, and three literals per clause.
Clauses are sets of literals, so a repeated literal in a printed three-literal clause is
represented once; the three witnesses retain that case. -/
def QBF.IsPaperQSAT (φ : QBF n m) : Prop :=
  0 < n ∧ Even n ∧
    (∀ j : Fin n, φ.q j = decide (Even j.val)) ∧
    (∀ i : Fin m, ∃ a b c : Fin n × Bool, φ.clause i = {a, b, c})

/-- The matrix `F` is true under the truth assignment `x`: every clause has a true literal. -/
def QBF.Sat (φ : QBF n m) (x : Fin n → Bool) : Prop :=
  ∀ i : Fin m, ∃ l ∈ φ.clause i, x l.1 = l.2

/-- The quantifier game from variable `k` on: the values of the variables before `k` are those of
`x`; then, in order, variable `k` is given a value by `∃` (if `q k`) or `∀` (otherwise), and so on
up to the last variable, after which `F` must be true. -/
def QBF.holdsFrom (φ : QBF n m) (k : ℕ) (x : Fin n → Bool) : Prop :=
  if h : k < n then
    if φ.q ⟨k, h⟩ then ∃ b : Bool, φ.holdsFrom (k + 1) (Function.update x ⟨k, h⟩ b)
    else ∀ b : Bool, φ.holdsFrom (k + 1) (Function.update x ⟨k, h⟩ b)
  else φ.Sat x
termination_by n - k

/-- The quantified formula is true: "there exists a truth value for x_1 such that, for all truth
values of x_2, etc. for all truth values of x_n, F comes out true" (p. 443). The starting
assignment is irrelevant, since every variable is overwritten before `F` is evaluated. -/
def QBF.holds (φ : QBF n m) : Prop :=
  φ.holdsFrom 0 (fun _ => false)

end MDPComplexity.PartiallyObserved


