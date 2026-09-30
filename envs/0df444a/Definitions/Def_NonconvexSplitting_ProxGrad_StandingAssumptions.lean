-- Prove2me | Definitions.Def_NonconvexSplitting_ProxGrad_StandingAssumptions
-- name    : NonconvexSplitting_ProxGrad_StandingAssumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T19:03:25.85033+00:00
-- url     : https://prove2.me/theorems/6b05a24d-31fe-4d4a-a0f4-3773d04ba476
-- title:
--   Standing assumptions on $h$ and $P$ (problem (1) with $\mathcal M = I$)
-- statement:
--   This file introduces three objects on $\mathbb{R}^n$.
--
--   1. The **Hessian** $\nabla^2 f(x)$ of $f : \mathbb{R}^n \to \mathbb{R}$, the derivative at $x$ of the gradient map $\nabla f$, a linear self-map of $\mathbb{R}^n$.
--   2. A function $f$ with values in $[-\infty, +\infty]$ is **proper** if it never equals $-\infty$ and is finite at some point.
--   3. The **standing assumptions** on a pair $(h, P)$, with $h : \mathbb{R}^n \to \mathbb{R}$ and $P : \mathbb{R}^n \to (-\infty, +\infty]$:
--      - $h$ is twice continuously differentiable with a bounded Hessian: $\sup_x \|\nabla^2 h(x)\| < \infty$;
--      - $P$ is proper and closed (lower semicontinuous);
--      - the proximal mappings are well-defined: for every $\tau > 0$ and every $u \in \mathbb{R}^n$,
--      $$
--      \operatorname*{Arg\,min}_y \Bigl\{ \tau P(y) + \tfrac12 \|y - u\|^2 \Bigr\} \neq \emptyset .
--      $$
--
--   These are the assumptions the paper places on problem (1) once and for all in its introduction, specialized to $\mathcal M = I$ (for which the surjectivity of $\mathcal M$ is automatic).
--
--   **Formalization Note** The operator norm of the Hessian is Mathlib's norm on continuous linear maps. The proximal objective is compared in `EReal`, with $\tau P(y)$ the `EReal` product of the positive real $\tau$ and $P(y)$.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, p. 1, standing assumptions on problem (1); p. 3, proper and closed

import Mathlib

namespace NonconvexSplitting.ProxGrad

/-- The Hessian `∇²f(x)` of `f : ℝⁿ → ℝ`, as the derivative of the gradient map. -/
noncomputable def hess {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ (gradient f) x

/-- A function with values in `(-∞, +∞]` is proper: it never equals `-∞` and is finite
somewhere (Li–Pong, p. 3). -/
def IsProperFn {X : Type*} (f : X → EReal) : Prop :=
  (∀ y, f y ≠ ⊥) ∧ ∃ y, f y ≠ ⊤

/-- The standing assumptions of Li–Pong (p. 1) on problem (1) in the case `M = I`:
`h` is twice continuously differentiable with a bounded Hessian; `P` is proper and closed
(lower semicontinuous); and for every `τ > 0` and every `u` the proximal problem
`min_y τ P(y) + ½‖y - u‖²` has at least one minimizer. -/
structure StandingAssumptions {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EReal) : Prop where
  h_contDiff : ContDiff ℝ 2 h
  hess_bounded : ∃ L : ℝ, ∀ x, ‖hess h x‖ ≤ L
  P_proper : IsProperFn P
  P_closed : LowerSemicontinuous P
  prox_nonempty : ∀ τ : ℝ, 0 < τ → ∀ u : EuclideanSpace ℝ (Fin n), ∃ y, ∀ z,
    (τ : EReal) * P y + ((‖y - u‖ ^ 2 / 2 : ℝ) : EReal) ≤
      (τ : EReal) * P z + ((‖z - u‖ ^ 2 / 2 : ℝ) : EReal)

end NonconvexSplitting.ProxGrad


