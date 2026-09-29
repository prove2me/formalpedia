-- Prove2me | Definitions.Def_CubicNewton_GradDom_omegaTilde
-- name    : CubicNewton_GradDom_omegaTilde
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:26:31.795286+00:00
-- url     : https://prove2.me/theorems/84269634-c1cd-498e-8cd0-24bd72287e5f
-- title:
--   The phase threshold $\tilde\omega = L_0^4/(324 (L+L_0)^6 \tau_f^3)$
-- statement:
--   For the Lipschitz constant $L$ of the Hessian, the lower bound $L_0$ on the regularization parameters of method (3.3), and the constant $\tau_f$ of gradient domination of degree $2$, set
--   $$\tilde\omega = \frac{L_0^4}{324\,(L + L_0)^6\,\tau_f^3} .$$
--   This is the threshold of Theorem 7, (4.14): while $f(x_k) - f(x^*) \ge \tilde\omega$ the method converges linearly, and below it superlinearly. It is positive whenever $L_0, L, \tau_f > 0$.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 194, Theorem 7, (4.14)

import Mathlib

namespace CubicNewton.GradDom

/-- The threshold `ω̃ = L₀⁴ / (324 (L + L₀)⁶ τ_f³)` of Nesterov–Polyak 2006, Theorem 7, (4.14),
p. 194, where `L` is the Lipschitz constant of the Hessian, `L₀ ∈ (0, L]` the lower bound on the
regularization parameters of method (3.3) and `τ_f` the constant of gradient domination (4.7). -/
noncomputable def omegaTilde (L₀ L τ : ℝ) : ℝ :=
  L₀ ^ 4 / (324 * (L + L₀) ^ 6 * τ ^ 3)

end CubicNewton.GradDom


