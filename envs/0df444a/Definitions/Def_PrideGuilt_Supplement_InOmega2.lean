-- Prove2me | Definitions.Def_PrideGuilt_Supplement_InOmega2
-- name    : PrideGuilt_Supplement_InOmega2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:19:54.472168+00:00
-- url     : https://prove2.me/theorems/06c872ea-449a-458f-bd26-5162f745d0c9
-- title:
--   Region $\Omega_2$ (guilt stronger than pride)
-- statement:
--   With $c_r$, $\Delta c$ and the demand coefficients $b_0,b_1$ of the model, the region $\Omega_2$ is the set of pairs $(\gamma_P,\gamma_G)$ with
--
--   $$
--   \gamma_P<\gamma_G\qquad\text{and}\qquad c_r-\Delta c\ \le\ \gamma_G\Bigl(1-\frac{b_1}{b_0}\Bigr).
--   $$
--
--   Here socially influenced guilt is stronger than pride and the degree of reluctance is low or moderate; Proposition 3 splits $\Omega_2$ into the sub-regions $\Omega_2^0$ and $\Omega_2^1$.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Proposition 3, p.14

import Mathlib
import Definitions.Def_PrideGuilt_cr
import Definitions.Def_PrideGuilt_dc

namespace PrideGuilt.Supplement

open PrideGuilt

/-- **The region `Ω₂` (guilt stronger than pride, low or moderate degree of reluctance).**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Proposition 3, p.14 (PDF 15):
`Ω₂ ≡ {(γ_P, γ_G) | γ_P < γ_G; c_r − Δc ≤ γ_G(1 − b₁/b₀)}`. -/
def InOmega2 (P : Params) (γP γG : ℝ) : Prop :=
  γP < γG ∧ cr P - dc P ≤ γG * (1 - P.b1 / P.b0)

end PrideGuilt.Supplement


