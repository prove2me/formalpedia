-- Prove2me | Definitions.Def_VehShare_MultiNet_workload
-- name    : VehShare_MultiNet_workload
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:35:30.250985+00:00
-- url     : https://prove2.me/theorems/b94a8a06-cc28-4bf1-a919-d9f58524e3fe
-- title:
--   Workload $\sum \Lambda_{ij}q_{ij}/\mu_{ij}$ of a static price vector
-- statement:
--   For a static vector of accepted fractions $q=(q_{ij})$, the **workload** is
--
--   $$
--   \sum_{(i,j)\in\mathcal A}\frac{\Lambda_{ij}q_{ij}}{\mu_{ij}},
--   $$
--
--   the left side of the workload constraint of Problem (2) (p. 5). For $q=q^s$ it is the constant $M$ of the proof of Theorem 4 (p. 18). Pairs with $\Lambda_{ij}=0$ contribute $0$.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, Problem (2), p. 5; proof of Theorem 4, p. 18

import Mathlib
import Definitions.Def_VehShare_MultiNet_meanTime

namespace VehShare.MultiNet

/-- **Workload of a static price vector.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), Problem (2), p. 5: `∑_{(i,j)∈𝒜} Λ_ij q_ij / μ_ij`; also `M = ∑_{(i,j)∈𝒜} Λ_ij q^s_ij/μ_ij`
in the proof of Theorem 4, p. 18.

**Formalization Note.** Summed over all pairs; pairs with `Λ_ij = 0` contribute 0. -/
noncomputable def workload (P : Instance) (q : P.L → P.L → ℝ) : ℝ :=
  ∑ i, ∑ j, P.Λ i j * q i j * meanTime P i j

end VehShare.MultiNet


