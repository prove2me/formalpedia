-- Prove2me | Definitions.Def_PrideGuilt_InOmega4
-- name    : PrideGuilt_InOmega4
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:09.074048+00:00
-- url     : https://prove2.me/theorems/2cab4163-77b3-4064-8efe-f217ad142d67
-- title:
--   Region $\Omega_4$
-- statement:
--   The pair $(\gamma_P,\gamma_G)$ lies in the region $\Omega_4$ when
--
--   $$
--   \Big(2-\frac{b_1}{b_0}\Big)\gamma_G-\gamma_P< c_r-\Delta c<\gamma_P-\frac{b_1\gamma_G}{b_0}.
--   $$
--
--   It is the region of a moderately high difficulty of remanufacturing $c_r-\Delta c$. Adding the two inequalities gives $\gamma_G<\gamma_P$: pride is stronger than guilt.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Proposition 5, p.15

import Mathlib
import Definitions.Def_PrideGuilt_cr
import Definitions.Def_PrideGuilt_dc

namespace PrideGuilt

/-- **The region `Ω₄`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Proposition 5, p.15 (PDF 16):
`Ω₄ ≡ {(γ_P, γ_G) | (2 − b₁/b₀)γ_G − γ_P < c_r − Δc < γ_P − b₁γ_G/b₀}`.

Adding the two inequalities gives `γ_G < γ_P` (stronger pride than guilt). -/
def InOmega4 (P : Params) (γP γG : ℝ) : Prop :=
  (2 - P.b1 / P.b0) * γG - γP < cr P - dc P ∧ cr P - dc P < γP - P.b1 * γG / P.b0

end PrideGuilt


