-- Prove2me | Definitions.Def_CubicNewton_Nonconvex_muMeasure
-- name    : CubicNewton_Nonconvex_muMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:14:52.208985+00:00
-- url     : https://prove2.me/theorems/91c92684-62e1-4063-b8f9-b5ac9eefbf26
-- title:
--   Second-order optimality measure $\mu_M(x)$
-- statement:
--   Let $f$ be twice differentiable with gradient $f'(x)$ and Hessian $f''(x)$, let $L > 0$ be the Lipschitz constant of the Hessian and $M > 0$ a parameter. The **measure of local optimality** at $x$ is
--   $$\mu_M(x) = \max\Big\{ \sqrt{\tfrac{2}{L + M}\,\|f'(x)\|},\ -\tfrac{2}{2L + M}\,\lambda_n(f''(x)) \Big\},$$
--   where $\lambda_n$ is the smallest eigenvalue. It is nonnegative, and it vanishes exactly at the points satisfying the second-order necessary conditions $f'(x) = 0$, $f''(x) \succeq 0$. The second entry is positive only when $f''(x)$ has a negative eigenvalue. With $M = L$ it reads $\mu_L(x) = \max\{\sqrt{\|f'(x)\|/L},\ -\tfrac{2}{3L}\lambda_n(f''(x))\}$, the measure in which Theorem 1 states its rate.
--
--   **Formalization Note** The formula is kept in the page's form, with $2/(L+M)$ inside the square root; $\lambda_n$ is `lamMin` (Rayleigh-quotient infimum).
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 184, Section 3 (definition of μM(x), after (3.2))

import Mathlib
import Definitions.Def_CubicNewton_Shared_lamMin

namespace CubicNewton.Nonconvex

/-- The measure of local (second-order) optimality of Nesterov–Polyak 2006, Section 3, p. 184:
`μ_M(x) = max { √( (2/(L + M)) ‖f′(x)‖ ), −(2/(2L + M)) λₙ(f″(x)) }`,
with `g x` for `f′(x)`, `H x` for `f″(x)` and `lamMin` for the smallest eigenvalue `λₙ`. -/
noncomputable def muMeasure {n : ℕ} (L M : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  max (Real.sqrt (2 / (L + M) * ‖g x‖)) (-(2 / (2 * L + M)) * CubicNewton.Shared.lamMin (H x))

end CubicNewton.Nonconvex


