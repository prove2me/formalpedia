-- Prove2me | Definitions.Def_AndOrSched_IsFeasible
-- name    : AndOrSched_IsFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:06.396774+00:00
-- url     : https://prove2.me/theorems/e13711d7-4986-4489-843f-db16d1948346
-- title:
--   Feasible schedules
-- statement:
--   A **schedule** assigns a completion time $C_j\in\mathbb R$ to every job; job $j$ is processed without preemption in $[C_j-p_j,C_j]$ on a single machine starting at time $0$. It is **feasible** if
--   1. $C_j\ge p_j$ for every $j$;
--   2. no two jobs overlap: $C_i\le C_j-p_j$ or $C_j\le C_i-p_i$ for $i\ne j$;
--   3. (AND-constraints) $C_j\ge C_i+p_j$ for every $(i,j)\in E_\wedge$;
--   4. (OR-constraints) $C_b\ge\min\{C_a\mid a\in\mathcal P(b)\}+p_b$ for every $b\in B$ with $\mathcal P(b)\ne\emptyset$.
--
--   Idle time is allowed.
--
--   **Formalization Note** The OR-constraint is written as "some $a\in\mathcal P(b)$ has $C_a+p_b\le C_b$", which is the same condition.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §1, pp.1–2, "A schedule C is feasible if (i) … and (ii) …"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_andRel
import Definitions.Def_AndOrSched_orPred
open scoped Classical NNReal

namespace AndOrSched

/-- A feasible schedule (Happach, Schulz, arXiv:2001.07011v1, §1, pp.1–2): a vector of completion times `C : N → ℝ` on a single
machine, each job processed non-preemptively for `pⱼ` time units in `[Cⱼ - pⱼ, Cⱼ]`, no two jobs
overlapping, with
(i) `Cⱼ ≥ max{Cᵢ | (i, j) ∈ E∧} + pⱼ` (AND-constraints) and
(ii) `C_b ≥ min{C_a | a ∈ 𝒫(b)} + p_b` for every `b ∈ B` with `𝒫(b) ≠ ∅` (OR-constraints).

**Formalization Note** The machine starts at time `0`, so `Cⱼ ≥ pⱼ`. Non-overlap of jobs `i ≠ j`
is `Cᵢ ≤ Cⱼ - pⱼ ∨ Cⱼ ≤ Cᵢ - pᵢ`. Idle time is allowed. The `min` in (ii) is written as
"some `a ∈ 𝒫(b)` has `C_a + p_b ≤ C_b`", which is the same condition. -/
def IsFeasible (I : Instance) (C : I.N → ℝ) : Prop :=
  (∀ j, ((I.p j : ℚ≥0) : ℝ) ≤ C j) ∧
  (∀ i j, i ≠ j → C i ≤ C j - (I.p j : ℝ) ∨ C j ≤ C i - (I.p i : ℝ)) ∧
  (∀ i j, andRel I i j → C i + (I.p j : ℝ) ≤ C j) ∧
  (∀ b, (orPred I b).Nonempty →
    ∃ a ∈ orPred I b, C (Sum.inl a) + (I.p (Sum.inr b) : ℝ) ≤ C (Sum.inr b))

end AndOrSched


