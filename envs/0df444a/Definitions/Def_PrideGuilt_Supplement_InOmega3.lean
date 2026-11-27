-- Prove2me | Definitions.Def_PrideGuilt_Supplement_InOmega3
-- name    : PrideGuilt_Supplement_InOmega3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:21:26.316761+00:00
-- url     : https://prove2.me/theorems/32e2620b-ffc9-4f8d-914f-cd70ed981fec
-- title:
--   Region $\Omega_3$ (pride stronger than guilt, low reluctance)
-- statement:
--   The region $\Omega_3$ is the set of pairs $(\gamma_P,\gamma_G)$ with
--
--   $$
--   \gamma_G<\gamma_P\qquad\text{and}\qquad c_r-\Delta c\ \le\ \Bigl(2-\frac{b_1}{b_0}\Bigr)\gamma_G-\gamma_P .
--   $$
--
--   Here pride is stronger than guilt and the degree of reluctance is low; Proposition 4 shows that the manufacturer induces perfect recycling.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), p.14 and Proposition 4, p.15

import Mathlib
import Definitions.Def_PrideGuilt_cr
import Definitions.Def_PrideGuilt_dc

namespace PrideGuilt.Supplement

open PrideGuilt

/-- **The region `Ω₃` (pride stronger than guilt, low degree of reluctance).**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, p.14 (PDF 15) and Proposition 4, p.15 (PDF 16):
`Ω₃ ≡ {(γ_P, γ_G) | γ_G < γ_P; c_r − Δc ≤ (2 − b₁/b₀)γ_G − γ_P}`. -/
def InOmega3 (P : Params) (γP γG : ℝ) : Prop :=
  γG < γP ∧ cr P - dc P ≤ (2 - P.b1 / P.b0) * γG - γP

end PrideGuilt.Supplement


