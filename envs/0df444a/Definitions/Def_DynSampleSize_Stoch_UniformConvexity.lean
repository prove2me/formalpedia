-- Prove2me | Definitions.Def_DynSampleSize_Stoch_UniformConvexity
-- name    : DynSampleSize_Stoch_UniformConvexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:27:40.106539+00:00
-- url     : https://prove2.me/theorems/4f980092-89db-4eab-8593-2d273550dd8a
-- title:
--   (4.2) — twice continuously differentiable, uniformly convex objective with Hessian bounds $\lambda, L$
-- statement:
--   Let $J:\mathbb R^m\to\mathbb R$ and let $\lambda, L$ be real constants. Following Byrd, Chin, Nocedal and Wu (p. 7, (4.2)), $J$ is **twice continuously differentiable and uniformly convex with constants $0<\lambda<L$** if $J$ is $C^2$, $0<\lambda<L$, and
--
--   $$
--   \lambda\|d\|_2^2 \;\le\; d^{T}\nabla^2 J(w)\,d \;\le\; L\|d\|_2^2 \qquad\text{for all } w, d\in\mathbb R^m .
--   $$
--
--   This is the standing assumption of §4 of the paper: it gives $J$ a unique minimizer $w^*$, and its two constants enter every rate in the analysis, through the step length $1/L$ and the condition number $L/\lambda$.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin m)`. Since `λ` is a Lean keyword the lower constant is named `lam`. The quadratic form $d^T\nabla^2J(w)d$ is the second Fréchet derivative `fderiv ℝ (fderiv ℝ J) w d d`; "twice continuously differentiable" is `ContDiff ℝ 2 J`.
-- source:
--   Byrd, Chin, Nocedal, Wu, Sample size selection in optimization methods for machine learning, Math. Program. (2012), doi:10.1007/s10107-012-0572-5 — authors' version of 18 Oct 2011, p. 7, (4.2)

import Mathlib

namespace DynSampleSize.Stoch

/-- Byrd–Chin–Nocedal–Wu (2012), p. 7, (4.2): `J : ℝ^m → ℝ` is twice continuously differentiable and
uniformly convex with constants `0 < lam < L` (the paper's `λ < L`):
`lam ‖d‖² ≤ dᵀ ∇²J(w) d ≤ L ‖d‖²` for all `w` and `d`. The Hessian quadratic form `dᵀ∇²J(w)d` is
the second Fréchet derivative `fderiv ℝ (fderiv ℝ J) w d d`. -/
def UniformlyConvex {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ) : Prop :=
  ContDiff ℝ 2 J ∧ 0 < lam ∧ lam < L ∧
    ∀ w d : EuclideanSpace ℝ (Fin m),
      lam * ‖d‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ J) w d d ∧ fderiv ℝ (fderiv ℝ J) w d d ≤ L * ‖d‖ ^ 2

end DynSampleSize.Stoch


