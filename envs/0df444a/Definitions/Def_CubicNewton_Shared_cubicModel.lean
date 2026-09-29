-- Prove2me | Definitions.Def_CubicNewton_Shared_cubicModel
-- name    : CubicNewton_Shared_cubicModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:13:10.04143+00:00
-- url     : https://prove2.me/theorems/9e7312b1-6733-49fa-baf5-968de15f8ddf
-- title:
--   Cubic regularization of the second-order model of $f$ at $x$
-- statement:
--   Let $f$ be a twice differentiable function on a subset of $\mathbb{R}^n$ with gradient $f'(x)$ and Hessian $f''(x)$, and let $M$ be a real parameter. The **cubic model** of $f$ at $x$ is the function of the trial point $y \in \mathbb{R}^n$
--   $$m_{M,x}(y) = \langle f'(x), y - x\rangle + \tfrac12\langle f''(x)(y - x), y - x\rangle + \tfrac{M}{6}\,\|y - x\|^3 .$$
--   It is the second-order Taylor approximation of $f(y) - f(x)$ plus a cubic regularization term. Nesterov and Polyak define the modified Newton step $T_M(x)$ as a global minimizer of this function (Eq. (2.4)), and the model value $\bar f_M(x) = f(x) + \min_y m_{M,x}(y)$.
--
--   Used by all four missions of this paper: 01-nonconvex (Sections 2–3, Theorem 1, pp. 180–185), 02-star-convex (Section 4.1, Theorem 4, pp. 188–189), 03-gradient-dominated (Section 4.2, Theorem 7, pp. 191–195) and 04-local-quadratic (method (3.5) and Theorem 3, pp. 186–188); in each it is the model of Eq. (2.4), p. 181.
--
--   **Formalization Note** The gradient and Hessian are passed as maps `g : E → E` and `H : E → (E →L[ℝ] E)` on `E = EuclideanSpace ℝ (Fin n)`; the definition uses only their values at $x$ and makes no claim that they are derivatives of anything.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 181, Section 2, Eq. (2.4)

import Mathlib

open scoped RealInnerProductSpace

namespace CubicNewton.Shared

/-- The cubic regularization of the second-order Taylor model of `f` at `x` (Nesterov–Polyak 2006,
p. 181, Eq. (2.4)), as a function of the trial point `y`:
`⟨f′(x), y − x⟩ + ½⟨f″(x)(y − x), y − x⟩ + (M/6)‖y − x‖³`.
Here `g x` plays the role of `f′(x)` and `H x` of `f″(x)`. -/
noncomputable def cubicModel {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪g x, y - x⟫ + (1 / 2) * ⟪H x (y - x), y - x⟫ + M / 6 * ‖y - x‖ ^ 3

end CubicNewton.Shared


