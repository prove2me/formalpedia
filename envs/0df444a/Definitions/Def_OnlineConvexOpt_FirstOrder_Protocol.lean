-- Prove2me | Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
-- name    : OnlineConvexOpt_FirstOrder_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:08:39.530105+00:00
-- url     : https://prove2.me/theorems/e69f1396-b934-42a5-be10-16d8a6b85b92
-- title:
--   OCO protocol: RegretT, metric projection, and online gradient descent runs
-- statement:
--   This item collects the shared machinery for Chapter III ("First-Order Algorithms for Online Convex Optimization"): the regret functional, the metric-projection predicate the algorithm's update rule uses, and the predicate that a decision/gradient pair is a run of online gradient descent.
--
--   **Regret.** For a decision set $K$ in a real inner product space $E$, a sequence of cost functions $f_t : E \to \mathbb{R}$, a sequence of played decisions $x_t \in K$, and a horizon $T$,
--   $$\mathrm{RegretT}(K, f, x, T) = \sum_{t=0}^{T-1} f_t(x_t) - \inf_{y \in K} \sum_{t=0}^{T-1} f_t(y),$$
--   exactly Eq. (1.1)/(1.2) of the book: the cumulative cost incurred by the algorithm's sequence of plays, minus the cost of the best fixed decision in hindsight. Here rounds are indexed $0, \dots, T-1$ (the book's rounds $1, \dots, T$ shifted down by one to match `Finset.range`).
--
--   **Metric projection.** `IsMetricProjection K y p` says $p \in K$ is a closest point of $K$ to $y$: $p \in K$ and $\operatorname{dist}(y, p) \le \operatorname{dist}(y, z)$ for every $z \in K$. This is the projection operator $\Pi_K$ used by Algorithm 8's update rule.
--
--   **Online gradient descent.** `IsOnlineGradientDescent K f \eta x g` says the decision sequence $x$ and the gradient sequence $g$ (with $g_t = \nabla f_t(x_t)$, recorded via Mathlib's `HasGradientAt`) form a run of Algorithm 8 with step sizes $\eta$: $x_0 \in K$, and at every round $t$, $g_t$ is a gradient of $f_t$ at $x_t$ and $x_{t+1}$ is a metric projection onto $K$ of the gradient step $x_t - \eta_t g_t$ — the book's $y_{t+1} = x_t - \eta_t \nabla_t$, $x_{t+1} = \Pi_K(y_{t+1})$.
--
--   **Formalization Note.** $K$ ranges over an arbitrary real inner product space `E` (`NormedAddCommGroup`, `InnerProductSpace ℝ`, `CompleteSpace`) rather than a fixed $\mathbb{R}^n$, since the chapter's arguments use only the Hilbert-space structure (inner products, the Pythagorean projection inequality). The projection predicate is existential/relational (`IsMetricProjection`) rather than a function, since Mathlib does not package a canonical nearest-point map for a general convex set.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 41, Eq. (1.1)/(1.2) (regret, restated from Chapter I §1); p. 43, Algorithm 8 (online gradient descent, PDF p. 65)

import Mathlib

namespace OnlineConvexOpt.FirstOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Regret of a decision sequence `x` against cost functions `f` over the first `T` rounds
(indexed `0, ..., T - 1`, i.e. the book's rounds `1, ..., T` shifted down by one), as in Eq.
(1.1)/(1.2): the cumulative cost incurred minus the cost of the best fixed decision in `K` in
hindsight. -/
noncomputable def RegretT (K : Set E) (f : ℕ → E → ℝ) (x : ℕ → E) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, f t (x t)) - ⨅ y ∈ K, ∑ t ∈ Finset.range T, f t y

/-- `p` is a metric projection of `y` onto `K`: a point of `K` at least as close to `y` as
every other point of `K`. This is the projection step `Π_K` used by Algorithm 8. -/
def IsMetricProjection (K : Set E) (y p : E) : Prop :=
  p ∈ K ∧ ∀ z ∈ K, dist y p ≤ dist y z

/-- `(x, g)` is a run of online gradient descent (Algorithm 8) on cost functions `f` over the
decision set `K`, with step sizes `η`: the initial decision `x 0` lies in `K`; at every round
`t`, `g t` is the gradient of `f t` at the played point `x t` (`∇t := ∇f_t(x_t)` in the book's
notation), and the next decision `x (t + 1)` is a metric projection onto `K` of the gradient
step `x t - η t • g t` (`y_{t+1} = x_t - η_t ∇_t`, `x_{t+1} = Π_K(y_{t+1})`). -/
def IsOnlineGradientDescent (K : Set E) (f : ℕ → E → ℝ) (η : ℕ → ℝ) (x g : ℕ → E) : Prop :=
  x 0 ∈ K ∧ ∀ t : ℕ, HasGradientAt (f t) (g t) (x t) ∧
    IsMetricProjection K (x t - η t • g t) (x (t + 1))

end OnlineConvexOpt.FirstOrder


