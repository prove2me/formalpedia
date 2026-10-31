-- Prove2me | Definitions.Def_PrideGuilt_UR
-- name    : PrideGuilt_UR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:41.459065+00:00
-- url     : https://prove2.me/theorems/1767f7a0-7369-4cdb-9344-8eeb2284c0bf
-- title:
--   Expected utility of a recycler $U_R$
-- statement:
--   In a community with recycling rate $\tau$ a consumer meets a recycler with probability $\tau$ and a non-recycler with probability $1-\tau$. A recycler earns the reward $f$, pays $c_e$, feels the intrinsic pride $I_P$, and gains the social pride $\gamma_P$ when meeting a non-recycler. Its expected utility (1) is
--
--   $$
--   U_R(f,\tau) = (f-c_e+I_P) + (1-\tau)\gamma_P .
--   $$
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), eq. (1), p.7

import Mathlib
import Definitions.Def_PrideGuilt_Params

namespace PrideGuilt

/-- **A recycler's expected utility (1), `U_R = (f − c_e + I_P) + (1 − τ)γ_P`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, eq. (1), p.7 (PDF 8).
`f` is the recycling reward, `τ` the recycling rate and `γP` the socially influenced pride. -/
def UR (P : Params) (γP f τ : ℝ) : ℝ := (f - P.ce + P.IP) + (1 - τ) * γP

end PrideGuilt


