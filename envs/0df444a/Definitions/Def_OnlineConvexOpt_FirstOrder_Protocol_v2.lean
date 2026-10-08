-- Prove2me | Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2
-- name    : OnlineConvexOpt_FirstOrder_Protocol_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:16:53.505958+00:00
-- url     : https://prove2.me/theorems/2f114fba-f88c-42ff-80b4-d8bc7cc15abb
-- title:
--   OCO protocol: regret (genuine infimum over K), metric projection, online gradient descent
-- statement:
--   The regret $\mathrm{Regret}_T=\sum_{t<T}f_t(x_t)-\inf\{\sum_{t<T}f_t(y):y\in K\}$ of a decision sequence against cost functions over a decision set $K$ (Eq. (1.1)), the metric projection onto $K$, and the run predicate of online gradient descent (Algorithm 8). Corrected version of `OnlineConvexOpt_FirstOrder_Protocol`: the comparator is the real infimum of the image of $K$ under the cumulative cost, instead of the bounded binder `⨅ y ∈ K, …`, which on $\mathbb R$ evaluates to the junk value $\inf\emptyset=0$ at every $y\notin K$ (so the retired regret was at least the whole cumulative cost for every bounded $K$). The infimum is the book's $\min_{y\in K}$ whenever $K$ is nonempty and the cumulative cost is bounded below on $K$; theorems using it carry those standing hypotheses. `IsMetricProjection` and `IsOnlineGradientDescent` are unchanged.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 2, Eq. (1.1)/(1.2) (regret); p. 43, Algorithm 8 (online gradient descent, PDF p. 65)

import Mathlib

namespace OnlineConvexOpt.FirstOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Regret of a decision sequence `x` against cost functions `f` over the first `T` rounds
(indexed `0, ..., T - 1`, i.e. the book's rounds `1, ..., T` shifted down by one), as in Eq.
(1.1)/(1.2) of Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3:
the cumulative cost incurred minus the cost of the best fixed decision in `K` in hindsight,
`∑_{t=1}^T f_t(x_t) - min_{y ∈ K} ∑_{t=1}^T f_t(y)`.

The comparator term is the real infimum of the *image* of `K` under the cumulative cost,
`sInf ((fun y => ∑ t ∈ range T, f t y) '' K)`. (The retired version wrote it as the bounded
binder `⨅ y ∈ K, …`, which on `ℝ` unfolds to `⨅ y, ⨅ (_ : y ∈ K), …` and evaluates the inner
infimum to the junk value `sInf ∅ = 0` at every `y ∉ K`, so the subtracted term was `≤ 0` for
every bounded `K`.) The image form is the book's `min_{y∈K}` whenever `K` is nonempty and the
cumulative cost is bounded below on `K` — both guaranteed by the standing OCO assumptions
(`K` nonempty and bounded, costs convex with bounded (sub)gradients, or costs bounded); for an
empty `K` or a cost unbounded below on `K` Mathlib's `sInf` still returns `0`, so every theorem
using `RegretT` must carry those standing hypotheses explicitly. -/
noncomputable def RegretT (K : Set E) (f : ℕ → E → ℝ) (x : ℕ → E) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, f t (x t)) - sInf ((fun y => ∑ t ∈ Finset.range T, f t y) '' K)

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


