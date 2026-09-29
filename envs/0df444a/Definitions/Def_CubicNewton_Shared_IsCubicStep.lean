-- Prove2me | Definitions.Def_CubicNewton_Shared_IsCubicStep
-- name    : CubicNewton_Shared_IsCubicStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:13:49.974985+00:00
-- url     : https://prove2.me/theorems/066bf797-1eac-4f33-9ca4-77d3936dce58
-- title:
--   Cubic-regularized Newton step $T_M(x)$: a global minimizer of the cubic model
-- statement:
--   Given the gradient and Hessian maps of $f$, a parameter $M$ and a point $x \in \mathbb{R}^n$, a point $T \in \mathbb{R}^n$ is a **cubic-regularized Newton step** from $x$ if it is a global minimizer of the cubic model:
--   $$\langle f'(x), T - x\rangle + \tfrac12\langle f''(x)(T - x), T - x\rangle + \tfrac{M}{6}\|T - x\|^3 \le \langle f'(x), y - x\rangle + \tfrac12\langle f''(x)(y - x), y - x\rangle + \tfrac{M}{6}\|y - x\|^3 \quad \text{for all } y \in \mathbb{R}^n.$$
--   This is the set $\operatorname{Arg\,min}_y$ of Eq. (2.4), from which the paper's $T_M(x)$ is chosen; "Arg" indicates that any global minimizer may be taken. For $M > 0$ the model is continuous and coercive, so the set is nonempty.
--
--   The results about $T_M(x)$ are stated for every point with this property, which is how the paper's arbitrary choice from the set of global minima is represented.
--
--   Used by all four missions of this paper: 01-nonconvex (Theorem 1, pp. 180–185), 02-star-convex (Theorem 4, pp. 188–189), 03-gradient-dominated (Theorem 7, pp. 191–195) and 04-local-quadratic (method (3.5) and Theorem 3, pp. 186–188); in each it is the step $T_M(x)$ of Eq. (2.4), p. 181.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 181, Section 2, Eq. (2.4)

import Mathlib
import Definitions.Def_CubicNewton_Shared_cubicModel

namespace CubicNewton.Shared

/-- `T` is a cubic-regularized Newton step from `x` with parameter `M` (Nesterov–Polyak 2006,
p. 181, Eq. (2.4)): `T` is a **global** minimizer of `y ↦ cubicModel g H M x y` over the whole
space. The paper's `T_M(x)` is any element of this set of global minima. -/
def IsCubicStep {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x T : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ y, cubicModel g H M x T ≤ cubicModel g H M x y

end CubicNewton.Shared


