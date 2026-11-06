-- Prove2me | Definitions.Def_IntervalToDynamic_proj
-- name    : IntervalToDynamic_proj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:53.4208+00:00
-- url     : https://prove2.me/theorems/1773e3ae-486b-45ba-80b5-0de29f5c626c
-- title:
--   The Euclidean projection $\Pi_{\mathcal X}[y]$
-- statement:
--   For a set $\mathcal X\subseteq\mathbb R^d$ and $y\in\mathbb R^d$, the projection is
--   $$
--   \Pi_{\mathcal X}[y]=\arg\min_{x\in\mathcal X}\|y-x\|_2 .
--   $$
--
--   Algorithm 1 plays the projection of the decision of the inner algorithm.
--
--   **Formalization Note** The function picks a metric projection by `Classical.epsilon`. For nonempty closed convex $\mathcal X$ a projection exists and is unique, so membership $\Pi_{\mathcal X}[y]\in\mathcal X$ is a fact to prove rather than an assumption. Every statement of the mission has such an $\mathcal X$.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Notation, p.4; Algorithm 1, p.8

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

namespace IntervalToDynamic

/-- The Euclidean projection `Π_X[y] = argmin_{x ∈ X} ‖y − x‖₂`. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Notation, p.4, as used in
Algorithm 1, p.8.

**Formalization Note.** `proj X y` chooses a point of `IsMetricProjection X y` by
`Classical.epsilon`. For a nonempty closed convex `X` such a point exists and is unique, so
`proj X y` is the projection and `proj X y ∈ X` is a fact to prove, not an assumption. For an `X`
without a projection of `y` the value is unspecified; every statement of this mission has `X`
nonempty, closed and convex. -/
noncomputable def proj {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  Classical.epsilon (OnlineConvexOpt.FirstOrder.IsMetricProjection X y)

end IntervalToDynamic


