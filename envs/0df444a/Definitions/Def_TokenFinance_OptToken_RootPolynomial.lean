-- Prove2me | Definitions.Def_TokenFinance_OptToken_RootPolynomial
-- name    : TokenFinance_OptToken_RootPolynomial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:25.331022+00:00
-- url     : https://prove2.me/theorems/c6258f0e-0865-4281-9a5b-9e305357c966
-- title:
--   The cubic $f(t)$ in equation (39)
-- statement:
--   Let $V=E_\theta[\pi^m]-C_0$ be the project's net present value. Define the cubic
--
--   $$f(t)=\frac{t^3}{3}-\frac{\theta-c}{2}t^2+\left(\frac{(\theta-c)^2}{4}+\frac{\theta}{2c}V\right)t-\frac\theta2 C_0.$$
--
--   This is the polynomial obtained from the token break-even equation in (39). It is used to establish uniqueness of the token pre-sale size. **Formalization Note** The project NPV remains an integral definition; its polynomial evaluation is a separate theorem.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 41 (PDF p. 42), (39)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.OptToken

/-- The cubic in equation (39), using the project's net present value. -/
noncomputable def rootPolynomial (c C0 θ t : ℝ) : ℝ :=
  t ^ 3 / 3 - t ^ 2 * ((θ - c) / 2) +
    t * ((θ - c) ^ 2 / 4 + θ / (2 * c) * TokenFinance.Debt.npv c C0 θ) - θ / 2 * C0

end TokenFinance.OptToken


