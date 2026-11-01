-- Prove2me | Definitions.Def_ExpConMinimax_Rconst
-- name    : ExpConMinimax_Rconst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:24.315012+00:00
-- url     : https://prove2.me/theorems/90cc96b0-b10e-454c-8ded-260fd3288f9b
-- title:
--   The constant $R$ of (3.13)
-- statement:
--   For constants $C_f,C_h,\sigma_h,C_g,\sigma_g$, an initial point $(x_0,y_0,\gamma_0,\lambda_0)$ and a saddle point $(x^*,y^*,\gamma^*,\lambda^*)$,
--   $$R=\frac{11C_f^2}{8C_h^2}+2\|\gamma_0-\gamma^*\|^2+\|\gamma^*\|\sigma_h+\frac{\sigma_h^2}{8}+\frac{19\|\gamma^*\|^2}{8}+2C_h^2\|x_0-x^*\|^2+4C_h^2\|x^*\|^2$$
--   $$\qquad+\frac{11C_f^2}{8C_g^2}+2\|\lambda_0-\lambda^*\|^2+\|\lambda^*\|\sigma_g+\frac{\sigma_g^2}{8}+\frac{19\|\lambda^*\|^2}{8}+2C_g^2\|y_0-y^*\|^2+4C_g^2\|y^*\|^2 .$$
--
--   $R$ bounds the second moments of the iterates (Proposition 7) and enters the rates of Theorem 9.
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, (3.13), p.14

import Mathlib
import Definitions.Def_ExpConMinimax_Vec

namespace ExpConMinimax

/-- **The constant `R` of (3.13)**, p.14.
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, Proposition 7 and (3.13), p.14:

`R = 11C_f²/(8C_h²) + 2‖γ₀ − γ*‖² + ‖γ*‖σ_h + σ_h²/8 + 19‖γ*‖²/8 + 2C_h²‖x₀ − x*‖² + 4C_h²‖x*‖²
   + 11C_f²/(8C_g²) + 2‖λ₀ − λ*‖² + ‖λ*‖σ_g + σ_g²/8 + 19‖λ*‖²/8 + 2C_g²‖y₀ − y*‖² + 4C_g²‖y*‖²`,

where `(x₀, y₀, γ₀, λ₀)` is the initial point of Algorithm 1 and `(x*, y*, γ*, λ*)` a saddle point
of (2.1). -/
noncomputable def Rconst {dx dy m₁ m₂ : ℕ} (Cf Ch σh Cg σg : ℝ) (x₀ : Vec dx) (y₀ : Vec dy)
    (γ₀ : Vec m₁) (lam₀ : Vec m₂) (xs : Vec dx) (ys : Vec dy) (γs : Vec m₁) (lams : Vec m₂) :
    ℝ :=
  11 * Cf ^ 2 / (8 * Ch ^ 2) + 2 * ‖γ₀ - γs‖ ^ 2 + ‖γs‖ * σh + σh ^ 2 / 8
    + 19 * ‖γs‖ ^ 2 / 8 + 2 * Ch ^ 2 * ‖x₀ - xs‖ ^ 2 + 4 * Ch ^ 2 * ‖xs‖ ^ 2
  + (11 * Cf ^ 2 / (8 * Cg ^ 2) + 2 * ‖lam₀ - lams‖ ^ 2 + ‖lams‖ * σg + σg ^ 2 / 8
    + 19 * ‖lams‖ ^ 2 / 8 + 2 * Cg ^ 2 * ‖y₀ - ys‖ ^ 2 + 4 * Cg ^ 2 * ‖ys‖ ^ 2)

end ExpConMinimax


