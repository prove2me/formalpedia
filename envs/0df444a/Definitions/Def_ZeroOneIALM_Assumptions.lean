-- Prove2me | Definitions.Def_ZeroOneIALM_Assumptions
-- name    : ZeroOneIALM_Assumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:53.904439+00:00
-- url     : https://prove2.me/theorems/128a053f-24d4-4612-808f-fa1f3fae9114
-- title:
--   Assumptions 1–5 on $f$ and $A$
-- statement:
--   The standing assumptions of the convergence analysis are the following.
--
--   1. **Assumption 1.** $f$ is $l_f$-smooth: $f$ is differentiable and $\|\nabla f(x)-\nabla f(y)\|\le l_f\|x-y\|$ for all $x,y$.
--   2. **Assumption 2.** $A$ has full row rank, used in the form: $\gamma>0$ and $\gamma\|z\|\le\|A^\top z\|$ for every $z\in\mathbb R^n$.
--   3. **Assumption 3.** $f$ is bounded below.
--   4. **Assumption 4.** $f$ is coercive: $f(w)\to\infty$ as $\|w\|\to\infty$.
--   5. **Assumption 5.** $f$ is strongly convex, with some positive modulus.
--
--   **Formalization Note** The paper fixes $\gamma:=\sqrt{\theta_{\min}(AA^\top)}$, with $\theta_{\min}$ the smallest eigenvalue. That constant satisfies the inequality above, since $\|A^\top z\|^2=z^\top AA^\top z\ge\theta_{\min}(AA^\top)\|z\|^2$, and any $\gamma>0$ satisfying it forces $A^\top$ to be injective. Coercivity is `Tendsto f (cocompact _) atTop`, which in the proper space $\mathbb R^p$ means $\|w\|\to\infty$.
-- source:
--   Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for Zero-One Composite Optimization, arXiv:2112.00440v1, Assumption 1, p.13, with p.5; Assumptions 2 and 3, p.16; Assumption 4, p.22, with p.7; Assumption 5, p.25

import Mathlib

open Filter

namespace ZeroOneIALM

variable {p n : ℕ}

/-- Assumption 1, Zhang & Xiu, arXiv:2112.00440v1, p.13, with the definition of `l_f`-smoothness
on p.5: `f` is differentiable and `‖∇f(x) - ∇f(y)‖ ≤ l_f ‖x - y‖` for all `x, y`.

**Formalization Note.** `∇f` is Mathlib's `gradient`, which is meaningful because differentiability
is part of the predicate. No sign is imposed on `l_f`. -/
def IsSmoothWith (f : EuclideanSpace ℝ (Fin p) → ℝ) (lf : ℝ) : Prop :=
  Differentiable ℝ f ∧ ∀ x y, ‖gradient f x - gradient f y‖ ≤ lf * ‖x - y‖

/-- The form in which Assumption 2, arXiv:2112.00440v1, p.16, is used: `γ > 0` and
`γ ‖z‖ ≤ ‖Aᵀz‖` for every `z`.

**Formalization Note.** The paper fixes `γ := √θ_min(AAᵀ)`, with `θ_min` the smallest eigenvalue.
That `γ` satisfies this predicate (`‖Aᵀz‖² = zᵀAAᵀz ≥ θ_min ‖z‖²`), and the predicate with some
`γ > 0` forces `Aᵀ` to be injective, that is, `A` to have full row rank. The constant `γ` is tied to
`A` by the inequality, and every use of Assumption 2 on pp.22–23 goes through this inequality. -/
def IsRowRankConstant (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)) (γ : ℝ) :
    Prop :=
  0 < γ ∧ ∀ z : EuclideanSpace ℝ (Fin n), γ * ‖z‖ ≤ ‖ContinuousLinearMap.adjoint A z‖

/-- Assumption 3, arXiv:2112.00440v1, p.16: `f` is bounded below. -/
def IsBoundedBelow (f : EuclideanSpace ℝ (Fin p) → ℝ) : Prop :=
  BddBelow (Set.range f)

/-- Assumption 4, arXiv:2112.00440v1, p.22, with the meaning given on p.7: `f` is coercive,
`lim_{‖w‖→∞} f(w) = ∞`.

**Formalization Note.** In the proper space `ℝᵖ` the cocompact filter is the filter `‖w‖ → ∞`. -/
def IsCoercive (f : EuclideanSpace ℝ (Fin p) → ℝ) : Prop :=
  Tendsto f (cocompact _) atTop

/-- Assumption 5, arXiv:2112.00440v1, p.25: `f` is strongly convex, with some positive modulus. -/
def IsStronglyConvex (f : EuclideanSpace ℝ (Fin p) → ℝ) : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ StrongConvexOn Set.univ σ f

end ZeroOneIALM


