-- Prove2me | Definitions.Def_OnlineConvexOpt_ChangingEnv_Regret
-- name    : OnlineConvexOpt_ChangingEnv_Regret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T17:30:40.559984+00:00
-- url     : https://prove2.me/theorems/41d17020-517f-4050-9b91-6c48db3a5b6f
-- title:
--   Path length, dynamic regret, interval regret, and adaptive regret
-- statement:
--   Four declarations for this chapter's core objects (§10.1-10.2). `PathLength u T` is
--   $P(u_1,\dots,u_T) = \sum_{t=1}^{T-1}\|u_t-u_{t+1}\| + 1$ (p. 170), the complexity of a
--   comparator sequence. `DynamicRegretT f x u T` is $\sum_{t=1}^T f_t(x_t) - \sum_{t=1}^T
--   f_t(u_t)$ (p. 170), regret against a *changing* comparator. `IntervalRegret K f x r s` is
--   the ordinary regret restricted to a contiguous round interval $[r,s]$. `AdaptiveRegretT K f
--   x T` (Definition 10.2, p. 172) is the supremum of `IntervalRegret` over every contiguous
--   sub-interval $[r,s]\subseteq[0,T-1]$ — the chapter's central new performance metric,
--   generalizing ordinary regret (the special case $[r,s]=[0,T-1]$) to demand low regret on
--   *every* sub-interval simultaneously.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 170-172 (PDF p. 192-194)

import Mathlib

namespace OnlineConvexOpt.ChangingEnv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The path length of a comparator sequence `u` up to horizon `T` (Hazan, *Introduction to
Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 170, PDF p. 192):
`P(u_1,...,u_T) = ∑_{t=1}^{T-1} ‖u_t - u_{t+1}‖ + 1`. Indexed `0,...,T-1` (the book's `1,...,T`
shifted down by one, matching `FirstOrder.Protocol`'s convention, which this chunk imports). -/
noncomputable def PathLength (u : ℕ → E) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range (T - 1), ‖u t - u (t + 1)‖) + 1

/-- The dynamic regret of a decision sequence `x` against a comparator sequence `u` (p. 170,
PDF p. 192): `DynamicRegretT(A,u_1,...,u_T) = ∑_{t=1}^T f_t(x_t) - ∑_{t=1}^T f_t(u_t)`. -/
noncomputable def DynamicRegretT (f : ℕ → E → ℝ) (x u : ℕ → E) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, f t (x t)) - ∑ t ∈ Finset.range T, f t (u t)

/-- The regret of `x` over the contiguous round interval `[r, s]` (p. 172, PDF p. 194, the
inner `Regret_{[r,s]}(A)` of Definition 10.2): `∑_{t=r}^s f_t(x_t) - min_{y∈K} ∑_{t=r}^s f_t(y)`. -/
noncomputable def IntervalRegret (K : Set E) (f : ℕ → E → ℝ) (x : ℕ → E) (r s : ℕ) : ℝ :=
  (∑ t ∈ Finset.Icc r s, f t (x t)) - ⨅ y ∈ K, ∑ t ∈ Finset.Icc r s, f t y

/-- Definition 10.2 (p. 172, PDF p. 194): the adaptive regret of `x` up to horizon `T` is the
supremum of `IntervalRegret` over every contiguous sub-interval `[r, s] ⊆ [0, T-1]` (the book's
`[1,T]` shifted). The supremum is over a finite, nonempty (for `T ≥ 1`) index set, so it is a
genuine maximum, not a real-suprema-of-an-unbounded-set junk value. -/
noncomputable def AdaptiveRegretT (K : Set E) (f : ℕ → E → ℝ) (x : ℕ → E) (T : ℕ) : ℝ :=
  ⨆ r ∈ Finset.range T, ⨆ s ∈ Finset.Icc r (T - 1), IntervalRegret K f x r s

end OnlineConvexOpt.ChangingEnv


