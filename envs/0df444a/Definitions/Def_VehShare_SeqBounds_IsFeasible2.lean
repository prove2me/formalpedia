-- Prove2me | Definitions.Def_VehShare_SeqBounds_IsFeasible2
-- name    : VehShare_SeqBounds_IsFeasible2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:40:40.088236+00:00
-- url     : https://prove2.me/theorems/0436c110-c294-444a-8e5c-a30b250e42fa
-- title:
--   Feasible set of Problem (2)
-- statement:
--   A static vector $q$ is **feasible for Problem (2)** with workload budget $\Delta$ if
--
--   1. $q_{ij}\in[0,1]$ for all $(i,j)$;
--   2. flows are balanced: $\sum_{j\in\mathcal N}\Lambda_{ij}q_{ij}=\sum_{j\in\mathcal N}\Lambda_{ji}q_{ji}$ for all $i$;
--   3. the workload is bounded: $\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}/\mu_{ij}\le\Delta$.
--
--   **Formalization Note** $q$ is given on all pairs; off $\mathcal A$ its values enter no constraint and no objective.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, Problem (2), p. 5

import Mathlib
import Definitions.Def_VehShare_SeqBounds_workload

namespace VehShare.SeqBounds

/-- **Feasible set of Problem (2).**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), Problem (2), p. 5: `∑_{j∈𝒩} Λ_ij q_ij = ∑_{j∈𝒩} Λ_ji q_ji` for all `i` in `𝒩`,
`∑_{(i,j)∈𝒜} Λ_ij q_ij/μ_ij ≤ Δ`, and `q_ij ∈ [0, 1]` for all `(i, j)` in `𝒜`.

**Formalization Note.** `q` is given (and bounded in `[0, 1]`) on all pairs; off `𝒜` its values
enter no constraint and no objective (factor `Λ_ij = 0`), so the feasible values on `𝒜` are the
paper's. -/
def IsFeasible2 (P : Instance) (Δ : ℝ) (q : P.L → P.L → ℝ) : Prop :=
  (∀ i j, 0 ≤ q i j ∧ q i j ≤ 1) ∧
    (∀ i, ∑ j, P.Λ i j * q i j = ∑ j, P.Λ j i * q j i) ∧
    workload P q ≤ Δ

end VehShare.SeqBounds


