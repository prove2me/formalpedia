-- Prove2me | Definitions.Def_PrideGuilt_tauMStar
-- name    : PrideGuilt_tauMStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:31.631418+00:00
-- url     : https://prove2.me/theorems/c0cc77a6-032a-4336-95e1-53640f6fc053
-- title:
--   Optimal interior recycling rate $\tau^*_m$
-- statement:
--   In $\Omega_4$ the optimal recycling rate is
--
--   $$
--   \tau^*_m\equiv\frac{b_0\Delta c-b_0c_r-b_1\gamma_G+b_0\gamma_P}{2b_0(\gamma_P-\gamma_G)}.
--   $$
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Proposition 5, p.15

import Mathlib
import Definitions.Def_PrideGuilt_cr
import Definitions.Def_PrideGuilt_dc

namespace PrideGuilt

/-- **The optimal interior recycling rate `τ*_m ≡ (b₀Δc − b₀c_r − b₁γ_G + b₀γ_P)/(2b₀(γ_P − γ_G))`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Proposition 5, p.15 (PDF 16). -/
noncomputable def tauMStar (P : Params) (γP γG : ℝ) : ℝ :=
  (P.b0 * dc P - P.b0 * cr P - P.b1 * γG + P.b0 * γP) / (2 * P.b0 * (γP - γG))

end PrideGuilt


