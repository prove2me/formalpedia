-- Prove2me | Definitions.Def_OnlineConvexOpt_ConvexBasics_ConstrainedGradientDescent
-- name    : OnlineConvexOpt_ConvexBasics_ConstrainedGradientDescent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T18:33:26.120307+00:00
-- url     : https://prove2.me/theorems/462e35df-9e63-4406-aa88-175fca32d624
-- title:
--   Constrained gradient descent with step size 1/β (Algorithm 4)
-- statement:
--   Let $E$ be a real inner product space, $K \subseteq E$ a decision set, $f : E \to \mathbb{R}$ an objective with global gradient map $g : E \to E$, and $\beta > 0$. The pair $(x, g)$, for a decision sequence $x : \mathbb{N} \to E$, is a run of **basic (projected) gradient descent** (Algorithm 4, book p. 27) on $K$ against $f$ with the constant step size $\eta_t = 1/\beta$ if $x_0 \in K$, $g$ is the gradient of $f$ everywhere, and at every round $t$, $x_{t+1}$ is a metric projection onto $K$ of the gradient step $x_t - \tfrac{1}{\beta} g(x_t)$:
--   $$y_{t+1} = x_t - \frac{1}{\beta}\, g(x_t), \qquad x_{t+1} = \Pi_K(y_{t+1}).$$
--
--   This is the constrained analogue of ordinary gradient descent: after the unconstrained update, the point is projected back onto $K$ so that every iterate stays feasible. The specific step size $\eta_t = 1/\beta$ (the reciprocal of the smoothness constant) is the one the book's Theorem 2.6 shows achieves linear convergence for well-conditioned objectives.
--
--   **Formalization Note.** The projection is `OnlineConvexOpt.FirstOrder.IsMetricProjection` (already published for Chapter III's Algorithm 8), reused rather than redeclared: `IsMetricProjection K y p` says $p \in K$ is at least as close to $y$ as every other point of $K$. `x` is 0-indexed, so the book's initial point $x_1 \in K$ (Algorithm 4 is 1-indexed) is `x 0`, and generally the book's $x_{k+1}$ is `x k`; theorems using this predicate restate the book's round-indexed conclusions accordingly.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 27, Algorithm 4 (PDF p. 49)

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

namespace OnlineConvexOpt.ConvexBasics

open OnlineConvexOpt.FirstOrder

/-- `(x, g)` is a run of basic (projected) gradient descent (Algorithm 4; Hazan, *Introduction to
Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 27, PDF p. 49) on decision set `K`
against `f`, with the constant step size `η t = 1 / β`: `x 0 ∈ K`, `g` is a global gradient map
for `f`, and at every round `t`, `x (t + 1)` is a metric projection onto `K` of the gradient step
`x t - (1 / β) • g (x t)` (the book's `y_{t+1} = x_t − η_t∇_t`, `x_{t+1} = Π_K(y_{t+1})`), reusing
`OnlineConvexOpt.FirstOrder.IsMetricProjection` (chapter III's published projection notion) rather
than redeclaring it. -/
def IsConstrainedGradientDescent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (K : Set E) (f : E → ℝ) (g : E → E) (β : ℝ) (x : ℕ → E) : Prop :=
  x 0 ∈ K ∧ (∀ z, HasGradientAt f (g z) z) ∧
    ∀ t : ℕ, IsMetricProjection K (x t - (1 / β) • g (x t)) (x (t + 1))

end OnlineConvexOpt.ConvexBasics


