-- Prove2me | Definitions.Def_VehShare_SeqBounds_Rs
-- name    : VehShare_SeqBounds_Rs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:39:34.615345+00:00
-- url     : https://prove2.me/theorems/6231d513-a922-41b5-a648-6c96288d8835
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
import Definitions.Def_VehShare_SeqBounds_Instance

namespace VehShare.SeqBounds

/-- **Fluid reward `R_s(q)` of a static price vector.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), Problem (2), p. 5: `R_s(q) = ∑_{(i,j)∈𝒜} Λ_ij q_ij I_ij(q_ij)`.

Pairs with `Λ_ij = 0` contribute 0. -/
def Rs (P : Instance) (q : P.L → P.L → ℝ) : ℝ :=
  ∑ i, ∑ j, P.Λ i j * q i j * P.I i j (q i j)

end VehShare.SeqBounds


