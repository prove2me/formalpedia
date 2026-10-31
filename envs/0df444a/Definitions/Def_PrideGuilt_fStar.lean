-- Prove2me | Definitions.Def_PrideGuilt_fStar
-- name    : PrideGuilt_fStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:53.185291+00:00
-- url     : https://prove2.me/theorems/c3e4b4a6-99de-4dc5-a066-3b470e9981b6
-- title:
--   Optimal reward $f^*$ in $\Omega_4$
-- statement:
--   In $\Omega_4$ the optimal recycling reward is
--
--   $$
--   f^*=\frac{b_0c_r+b_0\Delta c-b_1\gamma_G-b_0\gamma_P}{2b_0}.
--   $$
--
--   It may be negative.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Proposition 5, p.15

import Mathlib
import Definitions.Def_PrideGuilt_cr
import Definitions.Def_PrideGuilt_dc

namespace PrideGuilt

/-- **The optimal reward in `Ω₄`, `f* = (b₀c_r + b₀Δc − b₁γ_G − b₀γ_P)/(2b₀)`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Proposition 5, p.15 (PDF 16). -/
noncomputable def fStar (P : Params) (γP γG : ℝ) : ℝ :=
  (P.b0 * cr P + P.b0 * dc P - P.b1 * γG - P.b0 * γP) / (2 * P.b0)

end PrideGuilt


