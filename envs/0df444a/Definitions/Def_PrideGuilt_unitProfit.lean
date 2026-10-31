-- Prove2me | Definitions.Def_PrideGuilt_unitProfit
-- name    : PrideGuilt_unitProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:41.75398+00:00
-- url     : https://prove2.me/theorems/c2a34ddb-8c87-4240-b615-f26b37781bed
-- title:
--   Unit profit $u(p,f)$
-- statement:
--   The manufacturer's unit profit is the price less the expected unit production cost: a proportion $\tau^*(f)$ of units is remanufactured at cost $c_u+f$ (including the reward paid), the rest is made new at cost $c_n$:
--
--   $$
--   u(p,f)=p-\big(\tau^*(f)(c_u+f)+(1-\tau^*(f))c_n\big).
--   $$
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), below eq. (4), pp.11–12

import Mathlib
import Definitions.Def_PrideGuilt_tauStar

namespace PrideGuilt

/-- **The manufacturer's unit profit `u(p, f) ≡ p − (τ*(f)(c_u + f) + (1 − τ*(f))c_n)`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, below (4), pp.11–12 (PDF 12–13). -/
noncomputable def unitProfit (P : Params) (γP γG p f : ℝ) : ℝ :=
  p - (tauStar P γP γG f * (P.cu + f) + (1 - tauStar P γP γG f) * P.cn)

end PrideGuilt


