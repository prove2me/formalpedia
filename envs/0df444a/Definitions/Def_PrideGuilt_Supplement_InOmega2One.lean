-- Prove2me | Definitions.Def_PrideGuilt_Supplement_InOmega2One
-- name    : PrideGuilt_Supplement_InOmega2One
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:21:02.270451+00:00
-- url     : https://prove2.me/theorems/b63e91c3-aaec-4539-b330-78ca41344aa8
-- title:
--   Sub-region $\Omega_2^1$ (bandwagon toward perfect recycling)
-- statement:
--   With $\tilde\gamma=(1-\tau^0)\gamma_P+\tau^0\gamma_G$ as for $\Omega_2^0$, the sub-region $\Omega_2^1$ of $\Omega_2$ is the set of pairs $(\gamma_P,\gamma_G)\in\Omega_2$ with
--
--   $$
--   c_r-\Delta c\ \le\ \tilde\gamma\Bigl(1-\frac{b_1}{b_0}\Bigr)\ <\ \gamma_G\Bigl(1-\frac{b_1}{b_0}\Bigr).
--   $$
--
--   On $\Omega_2^1$ the manufacturer can afford a reward that tips the bandwagon toward perfect recycling (Proposition 3).
--
--   **Formalization Note** As for $\Omega_2^0$, membership in $\Omega_2$ is conjoined with the printed inequalities.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Proposition 3, p.14

import Mathlib
import Definitions.Def_PrideGuilt_Supplement_InOmega2

namespace PrideGuilt.Supplement

open PrideGuilt

/-- **The sub-region `Ω₂¹` of `Ω₂` (bandwagon toward perfect recycling).**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Proposition 3, p.14 (PDF 15):
`Ω₂¹ ≡ {(γ_P, γ_G) | c_r − Δc ≤ ((1 − τ⁰)γ_P + τ⁰γ_G)(1 − b₁/b₀) < γ_G(1 − b₁/b₀)}`.

**Formalization Note.** As for `InOmega2Zero`, membership in `Ω₂` is conjoined with the printed
inequalities, because the page introduces `Ω₂¹` as a part of `Ω₂`. -/
def InOmega2One (P : Params) (γP γG : ℝ) : Prop :=
  InOmega2 P γP γG ∧
    cr P - dc P ≤ ((1 - P.τ0) * γP + P.τ0 * γG) * (1 - P.b1 / P.b0) ∧
    ((1 - P.τ0) * γP + P.τ0 * γG) * (1 - P.b1 / P.b0) < γG * (1 - P.b1 / P.b0)

end PrideGuilt.Supplement


