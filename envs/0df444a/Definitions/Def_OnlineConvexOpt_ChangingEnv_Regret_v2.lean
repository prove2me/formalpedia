-- Prove2me | Definitions.Def_OnlineConvexOpt_ChangingEnv_Regret_v2
-- name    : OnlineConvexOpt_ChangingEnv_Regret_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:16:51.370398+00:00
-- url     : https://prove2.me/theorems/4f323aaf-7bb2-44f9-93bb-de9a92f4f637
-- title:
--   Path length, dynamic regret, interval regret and adaptive regret (genuine extrema)
-- statement:
--   The path length $P(u)=\sum_{t<T-1}\|u_t-u_{t+1}\|+1$ and dynamic regret of Chapter 10 (unchanged), the interval regret $\sum_{t=r}^{s}f_t(x_t)-\inf\{\sum_{t=r}^{s}f_t(y):y\in K\}$ and the adaptive regret of Definition 10.2, the supremum of the interval regrets over the finite set of contiguous intervals $[r,s]\subseteq[0,T-1]$ (a genuine maximum for $T\ge1$). Corrected version of `OnlineConvexOpt_ChangingEnv_Regret`: the comparator and the maximum are the real infimum/supremum of images instead of nested `⨅`/`⨆` binders, which on $\mathbb R$ return the junk value $0$ outside their index sets.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 170 (path length, dynamic regret), p. 172, Definition 10.2 (adaptive regret) (PDF pp. 192, 194)

import Mathlib

namespace OnlineConvexOpt.ChangingEnv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The path length of a comparator sequence `u` up to horizon `T` (Hazan, *Introduction to
Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 170, PDF p. 192):
`P(u_1,...,u_T) = ∑_{t=1}^{T-1} ‖u_t - u_{t+1}‖ + 1`. Indexed `0,...,T-1` (the book's `1,...,T`
shifted down by one, matching `FirstOrder.Protocol`'s convention). -/
noncomputable def PathLength (u : ℕ → E) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range (T - 1), ‖u t - u (t + 1)‖) + 1

/-- The dynamic regret of a decision sequence `x` against a comparator sequence `u` (p. 170,
PDF p. 192): `DynamicRegretT(A,u_1,...,u_T) = ∑_{t=1}^T f_t(x_t) - ∑_{t=1}^T f_t(u_t)`. -/
noncomputable def DynamicRegretT (f : ℕ → E → ℝ) (x u : ℕ → E) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, f t (x t)) - ∑ t ∈ Finset.range T, f t (u t)

/-- The regret of `x` over the contiguous round interval `[r, s]` (p. 172, PDF p. 194, the
inner `Regret_{[r,s]}(A)` of Definition 10.2): `∑_{t=r}^s f_t(x_t) - min_{y∈K} ∑_{t=r}^s f_t(y)`.
The comparator is the real infimum of the image of `K` under the interval cost (the retired
version used the binder `⨅ y ∈ K, …`, whose inner infimum is the junk value `sInf ∅ = 0` at every
`y ∉ K`); it is the book's `min_{y∈K}` whenever `K` is nonempty and the interval cost is bounded
below on `K`, which the theorems using it must guarantee by hypothesis. -/
noncomputable def IntervalRegret (K : Set E) (f : ℕ → E → ℝ) (x : ℕ → E) (r s : ℕ) : ℝ :=
  (∑ t ∈ Finset.Icc r s, f t (x t)) - sInf ((fun y => ∑ t ∈ Finset.Icc r s, f t y) '' K)

/-- Definition 10.2 (p. 172, PDF p. 194): the adaptive regret of `x` up to horizon `T` is the
maximum of `IntervalRegret` over every contiguous sub-interval `[r, s] ⊆ [0, T-1]` (the book's
`[1,T]` shifted), rendered as the real supremum of the image of the finite index set
`{(r, s) | r ≤ s < T}`. For `T ≥ 1` that set is finite and nonempty, so the supremum is a
genuine maximum. (The retired version used nested `⨆ r ∈ …, ⨆ s ∈ …` binders, which on `ℝ`
evaluate to the junk value `sSup ∅ = 0` outside the index set and so forced the adaptive regret
to be `≥ 0`.) -/
noncomputable def AdaptiveRegretT (K : Set E) (f : ℕ → E → ℝ) (x : ℕ → E) (T : ℕ) : ℝ :=
  sSup ((fun p : ℕ × ℕ => IntervalRegret K f x p.1 p.2) '' {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.2 < T})

end OnlineConvexOpt.ChangingEnv


