-- Prove2me | Definitions.Def_PrideGuilt_Supplement_InOmega2Zero
-- name    : PrideGuilt_Supplement_InOmega2Zero
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:20:28.980896+00:00
-- url     : https://prove2.me/theorems/d518398f-9064-5d2b-b1eb-7b275c122890
-- title:
--   Sub-region $\Omega_2^0$ (bandwagon toward no recycling)
-- statement:
--   Let $\tau^0$ be the initial proportion of recyclers and $\tilde\gamma=(1-\tau^0)\gamma_P+\tau^0\gamma_G$. The sub-region $\Omega_2^0$ of $\Omega_2$ is the set of pairs $(\gamma_P,\gamma_G)\in\Omega_2$ with
--
--   $$
--   \tilde\gamma\Bigl(1-\frac{b_1}{b_0}\Bigr)\ <\ c_r-\Delta c\ \le\ \gamma_G\Bigl(1-\frac{b_1}{b_0}\Bigr).
--   $$
--
--   On $\Omega_2^0$ the highest affordable reward cannot stop the bandwagon toward no recycling (Proposition 3).
--
--   **Formalization Note** The page introduces $\Omega_2^0$ and $\Omega_2^1$ as the two parts of $\Omega_2$, so membership in $\Omega_2$ (which adds $\gamma_P<\gamma_G$) is conjoined with the printed inequalities.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Proposition 3, p.14

import Mathlib
import Definitions.Def_PrideGuilt_Supplement_InOmega2

namespace PrideGuilt.Supplement

open PrideGuilt

/-- **The sub-region `Ω₂⁰` of `Ω₂` (bandwagon toward no recycling).**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Proposition 3, p.14 (PDF 15):
`Ω₂⁰ ≡ {(γ_P, γ_G) | ((1 − τ⁰)γ_P + τ⁰γ_G)(1 − b₁/b₀) < c_r − Δc ≤ γ_G(1 − b₁/b₀)}`.

**Formalization Note.** The page introduces `Ω₂⁰` and `Ω₂¹` as the two parts of `Ω₂` ("The
resulting ESE … is τ* = 0 in Ω₂⁰ and τ* = 1 in Ω₂¹", and the following paragraph: "In Ω₂ … i.e.,
in the sub-region Ω₂¹"), so the definition conjoins membership in `Ω₂` (which adds `γ_P < γ_G`)
with the printed inequalities. -/
def InOmega2Zero (P : Params) (γP γG : ℝ) : Prop :=
  InOmega2 P γP γG ∧
    ((1 - P.τ0) * γP + P.τ0 * γG) * (1 - P.b1 / P.b0) < cr P - dc P ∧
    cr P - dc P ≤ γG * (1 - P.b1 / P.b0)

end PrideGuilt.Supplement


