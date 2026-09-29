-- Prove2me | Definitions.Def_OnlineConvexOpt_SecondOrder_OnlineNewtonStep
-- name    : OnlineConvexOpt_SecondOrder_OnlineNewtonStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:30:30.62574+00:00
-- url     : https://prove2.me/theorems/46f47a4c-002f-4105-8231-cdd4b1291d1a
-- title:
--   Algorithm 12 — online Newton step and its generalized projection
-- statement:
--   Online Newton step (Algorithm 12) is a second-order algorithm for online convex
--   optimization against exp-concave losses. Given a decision set $K$, parameters
--   $\gamma, \varepsilon > 0$, and an initial point $x_0 \in K$, it maintains a running matrix
--   $A_t$ initialized at $A_0 = \varepsilon I$; at each round $t$ it plays $x_t$, observes the
--   gradient $\nabla_t = \nabla f_t(x_t)$, updates
--   $$
--   A_{t} = A_{t-1} + \nabla_t \nabla_t^\top ,
--   $$
--   takes the Newton step $y_{t+1} = x_t - \gamma^{-1} A_{t}^{-1}\nabla_t$, and projects back
--   onto $K$ in the norm induced by $A_t$ rather than the Euclidean norm:
--   $$
--   x_{t+1} = \Pi^{A_t}_K(y_{t+1}) = \arg\min_{x \in K} \|y_{t+1} - x\|_{A_t}^2 , \qquad
--   \|v\|_A^2 := \langle v, Av \rangle .
--   $$
--   This "generalized projection" — using the $A_t$-norm in place of the Euclidean norm of
--   online gradient descent — is what makes the Pythagorean inequality underlying the regret
--   proof hold with $A_t$ rather than the identity.
--
--   **Formalization Note** The matrix $A_t$ is represented as a continuous linear operator on
--   $E$ rather than as a `Matrix (Fin n) (Fin n) ℝ`; the rank-one update
--   $\nabla_t\nabla_t^\top$ is Mathlib's `InnerProductSpace.rankOne ℝ ∇_t ∇_t`
--   (the operator $v \mapsto \langle \nabla_t, v\rangle \nabla_t$), and $A_t^{-1}$ is
--   `ContinuousLinearMap.inverse`, Mathlib's total inverse (agreeing with the true inverse
--   whenever $A_t$ is invertible, which it always is here since every $A_t$ is positive
--   definite by construction). Round indices are shifted down by one from the source's
--   $t \in \{1, \dots, T\}$ to match the 0-indexed convention of `RegretT`.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 62, PDF p. 84, Algorithm 12

import Mathlib

namespace OnlineConvexOpt.SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The squared (semi)norm induced by an operator `A : E →L[ℝ] E`, `‖v‖²_A = ⟪v, A v⟫`. For the
positive semidefinite `A_t` of Algorithm 12 this is the norm `‖·‖_{A_t}` used by the algorithm's
generalized projection. -/
noncomputable def quadForm (A : E →L[ℝ] E) (v : E) : ℝ := inner ℝ v (A v)

/-- `IsGeneralizedProjection A K y p`: `p` is a minimizer over `K` of the squared distance to `y`
induced by `A`, i.e. `p ∈ arg min_{x ∈ K} ‖y - x‖²_A` — the projection `Π^A_K` of Algorithm 12
(book p. 62, PDF p. 84), in place of the Euclidean metric projection `Π_K` of online gradient
descent (`OnlineConvexOpt.FirstOrder.IsMetricProjection`). -/
def IsGeneralizedProjection (A : E →L[ℝ] E) (K : Set E) (y p : E) : Prop :=
  p ∈ K ∧ ∀ z ∈ K, quadForm A (y - p) ≤ quadForm A (y - z)

/-- `(x, g, A)` is a run of online Newton step (Algorithm 12, book p. 62, PDF p. 84) on cost
functions `f` over the decision set `K`, with parameters `γ, ε > 0`: the initial decision `x 0`
lies in `K`; `A 0 = ε • id` (`A_0 = εI_n`); at every round `t`, `g t` is the gradient of `f t` at
the played point `x t` (`∇t := ∇f_t(x_t)`); the running matrix updates by the rank-one term
`A (t + 1) = A t + ∇_t∇_t^⊤` (`InnerProductSpace.rankOne ℝ (g t) (g t)` is the operator
`v ↦ ⟪g t, v⟫ • g t`, matching the outer product); and the next decision `x (t + 1)` is the
`A (t + 1)`-generalized projection onto `K` of the Newton step
`y_{t+1} = x_t - γ⁻¹ A_{t+1}^{-1} ∇_t` (`(A (t + 1)).inverse` is Mathlib's total inverse of a
continuous linear map, agreeing with the matrix inverse when `A (t + 1)` is invertible, which
holds throughout the run since every `A (t + 1)` is positive definite: `A 0 ≻ 0` and each update
adds a positive semidefinite rank-one term). Indices are shifted down by one from the book's
`t ∈ {1, ..., T}` to match the 0-indexed convention of `OnlineConvexOpt.FirstOrder.RegretT`: our
`A (t + 1)` is the book's `A_{t+1}` built from rounds `1, ..., t+1`, i.e. our rounds `0, ..., t`. -/
def IsOnlineNewtonStep (K : Set E) (γ ε : ℝ) (f : ℕ → E → ℝ)
    (x g : ℕ → E) (A : ℕ → E →L[ℝ] E) : Prop :=
  x 0 ∈ K ∧ A 0 = ε • (ContinuousLinearMap.id ℝ E) ∧
    (∀ t : ℕ, HasGradientAt (f t) (g t) (x t)) ∧
    (∀ t : ℕ, A (t + 1) = A t + InnerProductSpace.rankOne ℝ (g t) (g t)) ∧
    (∀ t : ℕ, IsGeneralizedProjection (A (t + 1)) K
      (x t - γ⁻¹ • (A (t + 1)).inverse (g t)) (x (t + 1)))

end OnlineConvexOpt.SecondOrder


