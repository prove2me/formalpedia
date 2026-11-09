-- Prove2me | Definitions.Def_MWCSherali_Cnorm
-- name    : MWCSherali_Cnorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:15.115327+00:00
-- url     : https://prove2.me/theorems/120cf317-e99e-4038-b8c6-407249f77cc4
-- title:
--   The normalization constant $C$ (18)
-- statement:
--   $$C=\Big(\frac{(1-3\beta)^2}2-\frac{3(1-\alpha-2\beta)^2}2\Big)^{-1},\tag{18}$$
--
--   chosen so that $\nu_1(Z\cap\Gamma_1)=1$, i.e. $\nu_a$ is a probability measure.
--
--   **Formalization Note** Lean's inverse is $0$ at $0$; under Lemma 4.6's hypotheses the bracket (the area of the hexagon $Z\cap\Gamma_1$) is positive.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), (18), p.41

import Mathlib

namespace MWCSherali

/-- **The normalization constant `C`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), (18), p.41:
"`C = ((1 − 3β)²/2 − 3(1 − α − 2β)²/2)⁻¹`", chosen so that `ν₁(Z ∩ Γ₁) = 1`.

**Formalization Note.** Lean's `x⁻¹` is `0` at `x = 0`; under Lemma 4.6's hypotheses the
bracket is positive (it is the area of the hexagon `Z ∩ Γ₁`). -/
noncomputable def Cnorm (α β : ℝ) : ℝ :=
  ((1 - 3 * β) ^ 2 / 2 - 3 * (1 - α - 2 * β) ^ 2 / 2)⁻¹

end MWCSherali


