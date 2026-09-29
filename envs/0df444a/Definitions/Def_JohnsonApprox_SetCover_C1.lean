-- Prove2me | Definitions.Def_JohnsonApprox_SetCover_C1
-- name    : JohnsonApprox_SetCover_C1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:25:33.944105+00:00
-- url     : https://prove2.me/theorems/9d41f6b9-4be8-4c0e-abc9-98fc2c9a3c9a
-- title:
--   Algorithm C1 (greedy set cover) as a nondeterministic run relation, and choosable outputs (Section 5)
-- statement:
--   Algorithm C1 of Johnson (1974), p. 265, reads:
--
--   1. Set SUB $= \emptyset$, UNCOV $= \bigcup_{S \in F} S$, $N = |F|$, SET$[i] = S_i$, $1 \le i \le N$.
--   2. If UNCOV $= \emptyset$, halt and return SUB.
--   3. Choose $j \le N$ such that $|\mathrm{SET}[j]|$ is maximized.
--   4. Set SUB $=$ SUB $\cup \{S_j\}$, UNCOV $=$ UNCOV $-$ SET$[j]$, SET$[i] =$ SET$[i] -$ SET$[j]$, $1 \le i \le N$.
--   5. Go to 2.
--
--   A **state** of C1 consists of the variables SUB (a family of sets), UNCOV (a set of points) and the array SET. The **initial state** is the one after Step 1. The state $\sigma$ **halts** when UNCOV $= \emptyset$. One **step** from $\sigma$ to $\sigma'$ with choice $j$ is allowed when $\sigma$ does not halt, $|\mathrm{SET}[j]| \ge |\mathrm{SET}[i]|$ for every index $i$ (any maximizer may be chosen), and $\sigma'$ is obtained by Step 4: the original set $S_j$ is added to SUB, SET$[j]$ is removed from UNCOV and from every SET$[i]$.
--
--   Since Step 3 does not determine $j$ when there are ties, "more than one solution may be choosable for a given input" (p. 258). A family $F_1$ is **choosable by C1 given $F$** if some finite sequence of allowed steps leads from the initial state to a halting state whose SUB equals $F_1$.
--
--   The worst-case ratio of the paper is taken over all choosable outputs, so Theorem 4's upper bound quantifies over every choosable $F_1$.
--
--   **Formalization Note** The algorithm is a relation `Step S σ σ'` (existential over the index chosen at Step 3), and `Choosable S F₁` is `Relation.ReflTransGen (Step S) (init S) σ ∧ Halts σ ∧ σ.SUB = F₁`. No tie-breaking rule is fixed. The indices $1, \dots, N$ are the finite index type `ι` of the input.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 265, Section 5 (algorithm C1); p. 258, Section 2 (choosable solutions)

import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem

namespace JohnsonApprox.SetCover

/-!
Algorithm C1 (Johnson 1974, p. 265):
1. Set SUB = ∅, UNCOV = ⋃_{S∈F} S, N = |F|, SET[i] = S_i, 1 ≤ i ≤ N.
2. If UNCOV = ∅, halt and return SUB.
3. Choose j ≤ N such that |SET[j]| is maximized.
4. Set SUB = SUB ∪ {S_j}, UNCOV = UNCOV − SET[j], SET[i] = SET[i] − SET[j], 1 ≤ i ≤ N.
5. Go to 2.
Step 3 may pick any maximizer: the algorithm is a nondeterministic relation, not a function.
-/

variable {ι α : Type} [Fintype ι] [DecidableEq α]

/-- The variables of C1: `SUB` (the subfamily chosen so far), `UNCOV`, and the array `SET`
indexed by `ι` (the index set `{1, …, N}`, `N = |F|`). -/
structure State (ι α : Type) where
  SUB : Finset (Finset α)
  UNCOV : Finset α
  SET : ι → Finset α

/-- Step 1: `SUB = ∅`, `UNCOV = ⋃ S_i`, `SET[i] = S_i`. -/
def init (S : ι → Finset α) : State ι α := ⟨∅, ground S, S⟩

/-- The halting test of Step 2: `UNCOV = ∅`. -/
def Halts (σ : State ι α) : Prop := σ.UNCOV = ∅

/-- One pass through Steps 2–4 with the index `j` chosen at Step 3: C1 does not halt at Step 2,
`|SET[j]|` is maximal among all `|SET[i]|` (any maximizer may be chosen), and Step 4 sets
`SUB = SUB ∪ {S_j}` (the original set `S_j`), `UNCOV = UNCOV − SET[j]`,
`SET[i] = SET[i] − SET[j]` for every `i`. -/
def StepWith (S : ι → Finset α) (σ : State ι α) (j : ι) (σ' : State ι α) : Prop :=
  ¬ Halts σ ∧ (∀ i, (σ.SET i).card ≤ (σ.SET j).card) ∧
    σ' = ⟨insert (S j) σ.SUB, σ.UNCOV \ σ.SET j, fun i => σ.SET i \ σ.SET j⟩

/-- One iteration of C1 for some admissible choice at Step 3. -/
def Step (S : ι → Finset α) (σ σ' : State ι α) : Prop := ∃ j, StepWith S σ j σ'

/-- `F₁` is choosable by C1 given `F`: some admissible pass through the algorithm halts at
Step 2 and returns `SUB = F₁`. -/
def Choosable (S : ι → Finset α) (F₁ : Finset (Finset α)) : Prop :=
  ∃ σ, Relation.ReflTransGen (Step S) (init S) σ ∧ Halts σ ∧ σ.SUB = F₁

end JohnsonApprox.SetCover


