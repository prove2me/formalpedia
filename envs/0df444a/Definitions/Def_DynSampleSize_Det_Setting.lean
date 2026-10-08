-- Prove2me | Definitions.Def_DynSampleSize_Det_Setting
-- name    : DynSampleSize_Det_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:27:53.898039+00:00
-- url     : https://prove2.me/theorems/081ac413-dbcc-4cc6-a090-9aa83d2d7fd9
-- title:
--   Uniform convexity (4.2) with Hessian bounds $0<\lambda<L$, and the constant $\beta$ of (4.9)
-- statement:
--   Let $m \ge 0$ and let $J : \mathbb{R}^m \to \mathbb{R}$. Following §4.1 of Byrd, Chin, Nocedal and Wu, we say that $J$ satisfies **(4.2) with constants $\lambda, L$** if $J$ is twice continuously differentiable, $0 < \lambda < L$, and its Hessian is bounded above and below uniformly:
--
--   $$
--   \lambda\|d\|_2^2 \;\le\; d^T \nabla^2 J(w)\, d \;\le\; L\|d\|_2^2 \qquad \text{for all } w, d \in \mathbb{R}^m .
--   $$
--
--   Such a function is uniformly (strongly) convex with modulus $\lambda$ and has an $L$-Lipschitz gradient; it has a unique minimizer $w_*$.
--
--   For a parameter $\theta$ (in the paper $\theta \in (0,1)$), the constant of (4.9) is
--
--   $$
--   \beta(\theta) \;=\; \frac{(1-\theta)^2}{2(1+\theta)^2}.
--   $$
--
--   These two objects are shared by every statement of the mission: the inexact steepest descent iteration $w_{k+1} = w_k - \tfrac{1-\theta}{L} g_k$ contracts $J$ by the factor $1 - \beta\lambda/L$ per step.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin m)`. `lam` stands for the paper's $\lambda$ (a Lean keyword). The quadratic form $d^T\nabla^2 J(w) d$ is the second Fréchet derivative `fderiv ℝ (fderiv ℝ J) w d d`, and "twice continuously differentiable" is `ContDiff ℝ 2 J`. `HessianBounds J lam L` bundles `ContDiff ℝ 2 J`, `0 < lam`, `lam < L` and the two Hessian bounds; `beta θ` is $\beta(\theta)$.
-- source:
--   Byrd, Chin, Nocedal, Wu, Sample size selection in optimization methods for machine learning, Math. Program. (2012), doi:10.1007/s10107-012-0572-5 — authors' version of 18 Oct 2011, p. 7, (4.2); p. 8, (4.9)

import Mathlib

namespace DynSampleSize.Det

/-- The standing assumption (4.2) of §4.1, p. 7: `J : ℝ^m → ℝ` is twice continuously differentiable
and uniformly convex with Hessian bounds `0 < lam < L`, i.e.
`lam‖d‖² ≤ dᵀ∇²J(w)d ≤ L‖d‖²` for all `w, d`. (`lam` is the paper's `λ`; the Hessian quadratic
form `dᵀ∇²J(w)d` is the second Fréchet derivative applied to `(d, d)`.) -/
def HessianBounds {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ) : Prop :=
  ContDiff ℝ 2 J ∧ 0 < lam ∧ lam < L ∧
    ∀ w d : EuclideanSpace ℝ (Fin m),
      lam * ‖d‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ J) w d d ∧ fderiv ℝ (fderiv ℝ J) w d d ≤ L * ‖d‖ ^ 2

/-- The constant `β = (1 − θ)² / (2(1 + θ)²)` of (4.9), p. 8. -/
noncomputable def beta (θ : ℝ) : ℝ := (1 - θ) ^ 2 / (2 * (1 + θ) ^ 2)

end DynSampleSize.Det


