-- Prove2me | Definitions.Def_OnlineConvexOpt_ProjectionFree_ConditionalGradient
-- name    : OnlineConvexOpt_ProjectionFree_ConditionalGradient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:42:16.107341+00:00
-- url     : https://prove2.me/theorems/bd3d6647-cb71-4ecd-b0e5-274964d58c75
-- title:
--   Offline conditional gradient / Frank-Wolfe run (Algorithm 25)
-- statement:
--   `IsConditionalGradientRun K g η x v` formalizes a run of the (offline) conditional
--   gradient algorithm (Algorithm 25, p. 126): the initial point `x_1 ∈ K`, and at every round
--   `t ≥ 1`, `v_t` solves the linear-minimization oracle in the direction `g(x_t) = ∇f(x_t)`
--   (line 3), and the next point is the step `x_{t+1} = x_t + η_t(v_t - x_t)` (line 4). Indexed
--   from round `1` (the book's own convention), since this chapter's theorems state per-round
--   bounds directly rather than a cumulative sum over `Finset.range`.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 126, Algorithm 25 (PDF p. 148)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_LinearOracle

namespace OnlineConvexOpt.ProjectionFree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `(x, v)` is a run of the (offline) conditional gradient / Frank-Wolfe algorithm (Algorithm
25, Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 126,
PDF p. 148) on `K` with gradient map `g` and step sizes `η`: the initial point `x 1` lies in `K`,
and at every round `t ≥ 1`, `v t` solves the linear-minimization oracle in the direction `g (x
t)` (line 3: `v_t ← arg min_{x∈K}⟨x, ∇f(x_t)⟩`), and the next point is the step
`x_{t+1} = x_t + η_t(v_t - x_t)` (line 4). Indexed from `1` (not `0`), matching the book's own
`t ∈ [T]` indexing, since this chapter's theorems state per-round bounds `h_t ≤ ...` directly in
terms of the book's round number rather than a cumulative sum. -/
def IsConditionalGradientRun (K : Set E) (g : E → E) (η : ℕ → ℝ) (x v : ℕ → E) : Prop :=
  x 1 ∈ K ∧ ∀ t : ℕ, 1 ≤ t →
    IsLinearMinimizer K (g (x t)) (v t) ∧ x (t + 1) = x t + η t • (v t - x t)

end OnlineConvexOpt.ProjectionFree


