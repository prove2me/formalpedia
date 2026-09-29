-- Prove2me | Definitions.Def_JohnsonApprox_MaxSatWeighted_B2
-- name    : JohnsonApprox_MaxSatWeighted_B2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:13:23.78725+00:00
-- url     : https://prove2.me/theorems/0940f795-505e-43ad-925b-50bbf93b1f7e
-- title:
--   Algorithm B2 (Section 4): weighted literal selection as a nondeterministic run relation
-- statement:
--   Algorithm B2 of Johnson (1974), p. 263, reads:
--
--   1. Assign to each clause $C \in S$ a weight $w(C) = 2^{-|C|}$. Set $\mathrm{SUB} = \mathrm{TRUE} = \emptyset$, $\mathrm{LIT} = L$, and $\mathrm{LEFT} = S$.
--   2. If no literal in any clause of LEFT is in LIT, halt and return SUB.
--   3. Let $y$ be any literal occurring in both LIT and a clause of LEFT. Let YT be the set of clauses in LEFT and containing $y$, YF the set of clauses in LEFT containing $\bar y$.
--   4. If $\sum_{C\in \mathrm{YT}} w(C) \geq \sum_{C\in\mathrm{YF}} w(C)$, set $\mathrm{TRUE} = \mathrm{TRUE}\cup\{y\}$, $\mathrm{SUB} = \mathrm{SUB}\cup\mathrm{YT}$, $\mathrm{LEFT} = \mathrm{LEFT} - \mathrm{YT}$, and for each $C \in \mathrm{YF}$, set $w(C) = 2w(C)$. Otherwise, set $\mathrm{TRUE} = \mathrm{TRUE}\cup\{\bar y\}$, $\mathrm{SUB} = \mathrm{SUB}\cup\mathrm{YF}$, $\mathrm{LEFT} = \mathrm{LEFT} - \mathrm{YF}$, and for each $C\in\mathrm{YT}$, set $w(C) = 2w(C)$.
--   5. Set $\mathrm{LIT} = \mathrm{LIT} - \{y, \bar y\}$, and go to 2.
--
--   Because Step 3 lets $y$ be *any* admissible literal, the algorithm is not completely determined, and following Section 2 of the paper ("more than one solution may be choosable for a given input", p. 258) it is modelled as a relation. A **state** records SUB, LEFT, TRUE, the set of variables already considered, and the current weights $w$. The **initial state** is Step 1 on input $S$. A **step** $\sigma \to \sigma'$ holds when Step 2 does not halt in $\sigma$, $y$ is a literal of either sign whose variable has not yet been considered and which occurs in a clause of LEFT, and $\sigma'$ is the result of Steps 4–5 for that $y$, with the comparison and the doublings computed from the weights of $\sigma$. A set $X$ of clauses is **choosable by B2 on $S$** if some finite sequence of steps from the initial state reaches a state in which Step 2 halts and $\mathrm{SUB} = X$.
--
--   The ratio of Theorem 3 is taken at the worst choosable output, so every statement about B2 quantifies over all choosable outputs (for upper bounds) or exhibits one (for tightness).
--
--   **Formalization Note** The set $L$ of literals is infinite, so LIT is not stored; a literal is in LIT iff its variable is not in the finite set `decided`. Weights are a function `w : Clause → ℚ`, initially $1/2^{|C|}$ on every clause (only the clauses of $S$ ever matter). The tie in Step 4 goes to $y$ (`≤` on the YF side). A clause containing both $y$ and $\bar y$ lies in YT and YF, is removed with the chosen side and may be doubled as well, exactly as printed. `Reachable S σ` is the reflexive-transitive closure of `Step` from `init S`.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 263, Section 4 (algorithm B2); p. 258, Section 2

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem

namespace JohnsonApprox.MaxSatWeighted

/-- The state of algorithm B2: the paper's `SUB`, `LEFT`, `TRUE`, the set `decided` of variables
whose two literals have been removed from `LIT`, and the current clause weights `w`. Since `L` is
infinite, `LIT` is not stored: a literal `l` is in `LIT` iff `l.var ∉ decided`. -/
structure State where
  SUB : Finset Shared.Clause
  LEFT : Finset Shared.Clause
  TRUE : Finset Shared.Literal
  decided : Finset ℕ
  w : Shared.Clause → ℚ

/-- Membership in `LIT = L − ⋃ {y, ȳ}` over the literals `y` considered so far. -/
def State.inLIT (σ : State) (l : Shared.Literal) : Prop := l.var ∉ σ.decided

/-- Step 1 of B2: every clause `C` gets weight `w(C) = 2^{-|C|}`; `SUB = TRUE = ∅`, `LIT = L`
(no variable decided), `LEFT = S`. -/
def init (S : Finset Shared.Clause) : State := ⟨∅, S, ∅, ∅, fun C => 1 / 2 ^ C.card⟩

/-- `YT`: the clauses of `LEFT` containing the literal `y`. -/
def State.YT (σ : State) (y : Shared.Literal) : Finset Shared.Clause := σ.LEFT.filter (fun C => y ∈ C)

/-- `YF`: the clauses of `LEFT` containing the complementary literal `ȳ`. -/
def State.YF (σ : State) (y : Shared.Literal) : Finset Shared.Clause := σ.LEFT.filter (fun C => y.neg ∈ C)

/-- The total current weight `Σ_{C ∈ A} w(C)` of a set `A` of clauses. -/
def State.weight (σ : State) (A : Finset Shared.Clause) : ℚ := ∑ C ∈ A, σ.w C

/-- The weight function after setting `w(C) = 2w(C)` for each `C ∈ A`. -/
def doubleOn (w : Shared.Clause → ℚ) (A : Finset Shared.Clause) : Shared.Clause → ℚ :=
  fun C => if C ∈ A then 2 * w C else w C

/-- The halting test of Step 2: no literal in any clause of `LEFT` is in `LIT`. -/
def Halts (σ : State) : Prop := ∀ C ∈ σ.LEFT, ∀ l ∈ C, ¬ σ.inLIT l

/-- The state after Steps 4–5 of B2 with chosen literal `y`, computed from the weights before the
update. If `Σ_{C∈YT} w(C) ≥ Σ_{C∈YF} w(C)`: `TRUE = TRUE ∪ {y}`, `SUB = SUB ∪ YT`,
`LEFT = LEFT − YT`, and `w(C) = 2w(C)` for each `C ∈ YF`. Otherwise: `TRUE = TRUE ∪ {ȳ}`,
`SUB = SUB ∪ YF`, `LEFT = LEFT − YF`, and `w(C) = 2w(C)` for each `C ∈ YT`. In both cases
`LIT = LIT − {y, ȳ}`. -/
def State.update (σ : State) (y : Shared.Literal) : State :=
  if σ.weight (σ.YF y) ≤ σ.weight (σ.YT y) then
    ⟨σ.SUB ∪ σ.YT y, σ.LEFT \ σ.YT y, insert y σ.TRUE, insert y.var σ.decided,
      doubleOn σ.w (σ.YF y)⟩
  else
    ⟨σ.SUB ∪ σ.YF y, σ.LEFT \ σ.YF y, insert y.neg σ.TRUE, insert y.var σ.decided,
      doubleOn σ.w (σ.YT y)⟩

/-- One pass through Steps 2–5 of B2 with chosen literal `y`: Step 2 does not halt; Step 3 lets
`y` be any literal (of either sign) occurring both in `LIT` and in a clause of `LEFT`; Steps 4–5
produce `σ'`. -/
def StepWith (σ : State) (y : Shared.Literal) (σ' : State) : Prop :=
  ¬ Halts σ ∧ σ.inLIT y ∧ (∃ C ∈ σ.LEFT, y ∈ C) ∧ σ' = σ.update y

/-- One iteration of B2, for some admissible choice of `y`. -/
def Step (σ σ' : State) : Prop := ∃ y, StepWith σ y σ'

/-- `σ` is a state B2 can be in after finitely many iterations on input `S`. -/
def Reachable (S : Finset Shared.Clause) (σ : State) : Prop := Relation.ReflTransGen Step (init S) σ

/-- `X` is choosable by B2 on input `S`: some admissible run halts and returns `SUB = X`. -/
def Choosable (S : Finset Shared.Clause) (X : Finset Shared.Clause) : Prop :=
  ∃ σ, Reachable S σ ∧ Halts σ ∧ σ.SUB = X

end JohnsonApprox.MaxSatWeighted


