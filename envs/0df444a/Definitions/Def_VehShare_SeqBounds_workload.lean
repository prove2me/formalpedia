-- Prove2me | Definitions.Def_VehShare_SeqBounds_workload
-- name    : VehShare_SeqBounds_workload
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:34:02.562251+00:00
-- url     : https://prove2.me/theorems/529b95de-1e03-49dc-b66a-a01af923d7c8
-- title:
--   Workload $\sum \Lambda_{ij}q_{ij}/\mu_{ij}$ of a static price vector
-- statement:
--   For a static vector of accepted fractions $q=(q_{ij})$, the **workload** is
--
--   $$
--   \sum_{(i,j)\in\mathcal A}\frac{\Lambda_{ij}q_{ij}}{\mu_{ij}},
--   $$
--
--   the left side of the workload constraint of Problem (2) (p. 5). For $q=q^s$ it is the constant $\lambda/\mu=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q^s_{ij}/\mu_{ij}$ of Theorem 2 (p. 9). Pairs with $\Lambda_{ij}=0$ contribute $0$.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, Problem (2), p. 5; Theorem 2, p. 9

import Mathlib
import Definitions.Def_VehShare_SeqBounds_meanTime

namespace VehShare.SeqBounds

/-- **Workload of a static price vector.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), Problem (2), p. 5: `∑_{(i,j)∈𝒜} Λ_ij q_ij / μ_ij`; at `q = q^s` it is the constant
`λ/μ = ∑_{(i,j)∈𝒜} Λ_ij q^s_ij/μ_ij` of Theorem 2, p. 9.

**Formalization Note.** Summed over all pairs; pairs with `Λ_ij = 0` contribute 0. -/
noncomputable def workload (P : Instance) (q : P.L → P.L → ℝ) : ℝ :=
  ∑ i, ∑ j, P.Λ i j * q i j * meanTime P i j

end VehShare.SeqBounds


