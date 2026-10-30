-- Prove2me | Definitions.Def_VehShare_MultiNet_Rs
-- name    : VehShare_MultiNet_Rs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:41:23.825136+00:00
-- url     : https://prove2.me/theorems/7fe7b44a-3369-4e17-99b8-b8f2b92a44fa
-- title:
--   Fluid reward $R_s(q)$ of Problem (2)
-- statement:
--   For a static vector of accepted fractions $q$, the **fluid reward** is the objective of Problem (2) (p. 5):
--
--   $$
--   R_s(q)=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}I_{ij}(q_{ij}).
--   $$
--
--   It is the reward rate when vehicles are always available.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, Problem (2), p. 5

import Mathlib
import Definitions.Def_VehShare_MultiNet_Instance

namespace VehShare.MultiNet

/-- **Fluid reward `R_s(q)` of a static price vector.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), Problem (2), p. 5: `R_s(q) = ∑_{(i,j)∈𝒜} Λ_ij q_ij I_ij(q_ij)`.

Pairs with `Λ_ij = 0` contribute 0. -/
def Rs (P : Instance) (q : P.L → P.L → ℝ) : ℝ :=
  ∑ i, ∑ j, P.Λ i j * q i j * P.I i j (q i j)

end VehShare.MultiNet


