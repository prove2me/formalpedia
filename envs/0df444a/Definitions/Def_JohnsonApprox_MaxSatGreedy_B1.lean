-- Prove2me | Definitions.Def_JohnsonApprox_MaxSatGreedy_B1
-- name    : JohnsonApprox_MaxSatGreedy_B1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:20:57.956346+00:00
-- url     : https://prove2.me/theorems/5fa93e41-09ae-4722-853a-b2561cccc708
-- title:
--   Algorithm B1 (greedy literal selection) as a nondeterministic run relation (Section 4)
-- statement:
--   Algorithm B1 of Johnson (1974), Section 4, as printed on p. 262:
--
--   1. Set SUB $= \emptyset$, TRUE $= \emptyset$, LEFT $= S$, LIT $= L$.
--   2. If no literal in LIT is contained in any clause of LEFT, halt and return SUB.
--   3. Let $y$ be the literal in LIT which is contained in the most clauses of LEFT, and YT be the set of clauses in LEFT which contain $y$.
--   4. Set SUB $=$ SUB $\cup$ YT, LEFT $=$ LEFT $-$ YT, TRUE $=$ TRUE $\cup \{y\}$, and LIT $=$ LIT $- \{y, \bar y\}$.
--   5. Go to 2.
--
--   A **state** records SUB, LEFT, TRUE and the set of variables already decided; a literal lies in LIT exactly when its variable has not been decided. The **initial state** is that of Step 1 on input $S$. A **step** from state $\sigma$ to $\sigma'$ with chosen literal $y$ is possible when Step 2 does not halt at $\sigma$, $y$ is in LIT, and no literal of LIT lies in more clauses of LEFT than $y$ does; $\sigma'$ is then the result of Step 4. Every maximizing literal of either sign may be chosen, because the paper's framework (p. 258) says that "more than one solution may be choosable for a given input". A set $X$ of clauses is **choosable by B1 on $S$** if some finite sequence of steps from the initial state reaches a state at which Step 2 halts and SUB $= X$.
--
--   By p. 258–259, the performance of B1 on $S$ is the minimum of $|X|$ over choosable $X$, so worst-case statements about B1 quantify over every choosable output.
--
--   **Formalization Note** The literal set $L$ is infinite, so LIT is not stored; the state keeps the finite set `decided` of variables whose two literals have been removed, and `inLIT l` means `l.var ∉ decided`. `StepWith σ y σ'` is one iteration with choice $y$, `Step` hides the choice, `Reachable S σ` is the reflexive–transitive closure from `init S`, and `Choosable S X` asks for a reachable halting state with `SUB = X`. Ties are resolved existentially, never by a fixed rule.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 262, Section 4 (algorithm B1); p. 258, Section 2

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem

namespace JohnsonApprox.MaxSatGreedy

/-- The state of algorithm B1: the paper's `SUB`, `LEFT`, `TRUE`, and the set `decided` of
variables whose two literals have been removed from `LIT`. Since `L` is infinite, `LIT` is not
stored: a literal `l` is in `LIT` iff `l.var ∉ decided`. -/
structure State where
  SUB : Finset Shared.Clause
  LEFT : Finset Shared.Clause
  TRUE : Finset Shared.Literal
  decided : Finset ℕ

/-- Membership in `LIT = L − ⋃ {y, ȳ}` over the literals `y` chosen so far. -/
def State.inLIT (σ : State) (l : Shared.Literal) : Prop := l.var ∉ σ.decided

/-- Step 1 of B1: `SUB = ∅`, `TRUE = ∅`, `LEFT = S`, `LIT = L` (no variable decided). -/
def init (S : Finset Shared.Clause) : State := ⟨∅, S, ∅, ∅⟩

/-- `YT`: the clauses of `LEFT` containing the literal `y`. -/
def State.YT (σ : State) (y : Shared.Literal) : Finset Shared.Clause := σ.LEFT.filter (fun C => y ∈ C)

/-- The number of clauses of `LEFT` containing the literal `l`. -/
def State.count (σ : State) (l : Shared.Literal) : ℕ := (σ.YT l).card

/-- The halting test of Step 2: no literal in `LIT` is contained in any clause of `LEFT`. -/
def Halts (σ : State) : Prop := ∀ C ∈ σ.LEFT, ∀ l ∈ C, ¬ σ.inLIT l

/-- One pass through Steps 2–4 of B1 with chosen literal `y`: Step 2 does not halt; Step 3 lets
`y` be a literal in `LIT` contained in the most clauses of `LEFT` (any maximizer, of either sign);
Step 4 sets `SUB = SUB ∪ YT`, `LEFT = LEFT − YT`, `TRUE = TRUE ∪ {y}`, `LIT = LIT − {y, ȳ}`. -/
def StepWith (σ : State) (y : Shared.Literal) (σ' : State) : Prop :=
  ¬ Halts σ ∧ σ.inLIT y ∧ (∀ z : Shared.Literal, σ.inLIT z → σ.count z ≤ σ.count y) ∧
    σ' = ⟨σ.SUB ∪ σ.YT y, σ.LEFT \ σ.YT y, insert y σ.TRUE, insert y.var σ.decided⟩

/-- One iteration of B1, for some admissible choice of `y`. -/
def Step (σ σ' : State) : Prop := ∃ y, StepWith σ y σ'

/-- `σ` is a state B1 can be in after finitely many iterations on input `S`. -/
def Reachable (S : Finset Shared.Clause) (σ : State) : Prop := Relation.ReflTransGen Step (init S) σ

/-- `X` is choosable by B1 on input `S`: some admissible run halts with `SUB = X`. -/
def Choosable (S : Finset Shared.Clause) (X : Finset Shared.Clause) : Prop :=
  ∃ σ, Reachable S σ ∧ Halts σ ∧ σ.SUB = X

end JohnsonApprox.MaxSatGreedy


