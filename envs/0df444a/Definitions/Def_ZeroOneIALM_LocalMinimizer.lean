-- Prove2me | Definitions.Def_ZeroOneIALM_LocalMinimizer
-- name    : ZeroOneIALM_LocalMinimizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:28:30.954992+00:00
-- url     : https://prove2.me/theorems/be47c726-f8ed-4a33-8dab-8f60259cffa2
-- title:
--   The objective and the local minimizers of problem (2)
-- statement:
--   Problem (2) is
--   $$
--   \min_{w\in\mathbb R^p,\,u\in\mathbb R^n}\ f(w)+\lambda\|u_+\|_0\quad\text{s.t.}\quad Aw+b=u,
--   $$
--   with $A\in\mathbb R^{n\times p}$ and $b\in\mathbb R^n$.
--
--   A pair $(w^*;u^*)$ is a **local minimizer** of (2) if it is feasible, $Aw^*+b=u^*$, and there is $\delta>0$ such that
--   $$
--   f(w^*)+\lambda\|u^*_+\|_0\le f(w)+\lambda\|u_+\|_0
--   $$
--   for every feasible $(w;u)$ with $\|w-w^*\|^2+\|u-u^*\|^2<\delta^2$.
--
--   The comparison runs over feasible pairs only. This is the sense in which the limit of the algorithm is a local minimizer.
--
--   **Formalization Note** The paper uses this standard notion without spelling it out. The matrix $A$ is a continuous linear map between Euclidean spaces.
-- source:
--   Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for Zero-One Composite Optimization, arXiv:2112.00440v1, p.1, problem (2); p.4, neighbourhoods

import Mathlib
import Definitions.Def_ZeroOneIALM_ZeroOneLoss

namespace ZeroOneIALM

variable {p n : ℕ}

/-- The objective `f(w) + λ‖u₊‖₀` of problem (2), Zhang & Xiu, arXiv:2112.00440v1, p.1. -/
noncomputable def objective (f : EuclideanSpace ℝ (Fin p) → ℝ) (lam : ℝ)
    (w : EuclideanSpace ℝ (Fin p)) (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f w + lam * posCount u

/-- `(w*; u*)` is a local minimizer of problem (2), arXiv:2112.00440v1, p.1: it is feasible,
`Aw* + b = u*`, and its objective value is least among the feasible pairs in a neighbourhood.

**Formalization Note.** The paper does not spell this notion out; this is the standard one for a
constrained problem, so the comparison runs over feasible pairs only. The neighbourhood is the ball
of radius `δ` in `ℝᵖ × ℝⁿ` with the Euclidean norm, as in `N(·; δ)` on p.4, written
`‖w - w*‖² + ‖u - u*‖² < δ²`. The matrix `A ∈ ℝⁿˣᵖ` is a continuous linear map between Euclidean
spaces. -/
def IsLocalMinimizer (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (lam : ℝ)
    (wstar : EuclideanSpace ℝ (Fin p)) (ustar : EuclideanSpace ℝ (Fin n)) : Prop :=
  A wstar + b = ustar ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ (w : EuclideanSpace ℝ (Fin p)) (u : EuclideanSpace ℝ (Fin n)),
      A w + b = u → ‖w - wstar‖ ^ 2 + ‖u - ustar‖ ^ 2 < δ ^ 2 →
        objective f lam wstar ustar ≤ objective f lam w u

end ZeroOneIALM


