-- Prove2me | Definitions.Def_PrideGuilt_pStar
-- name    : PrideGuilt_pStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:42.858328+00:00
-- url     : https://prove2.me/theorems/76283c3e-3522-4065-9f93-5ea5cc52463b
-- title:
--   Optimal price $p^*$ in $\Omega_4$
-- statement:
--   In $\Omega_4$ the optimal selling price is
--
--   $$
--   p^*=\frac{1-b_1I_G}{2b_0}+\frac{c_n}{2}-\frac{(b_0\Delta c-b_0c_r+b_0\gamma_P+b_1\gamma_G)^2-4b_1^2\gamma_G^2}{8b_0^2(\gamma_P-\gamma_G)}.
--   $$
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Proposition 5, p.15

import Mathlib
import Definitions.Def_PrideGuilt_cr
import Definitions.Def_PrideGuilt_dc

namespace PrideGuilt

/-- **The optimal price in `Ω₄`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Proposition 5, p.15 (PDF 16):
`p* = (1 − b₁I_G)/(2b₀) + c_n/2 − ((b₀Δc − b₀c_r + b₀γ_P + b₁γ_G)² − 4b₁²γ_G²)/(8b₀²(γ_P − γ_G))`. -/
noncomputable def pStar (P : Params) (γP γG : ℝ) : ℝ :=
  (1 - P.b1 * P.IG) / (2 * P.b0) + P.cn / 2 -
    ((P.b0 * dc P - P.b0 * cr P + P.b0 * γP + P.b1 * γG) ^ 2 - 4 * P.b1 ^ 2 * γG ^ 2) /
      (8 * P.b0 ^ 2 * (γP - γG))

end PrideGuilt


