-- Prove2me | Definitions.Def_OnlineConvexOpt_ProjectionFree_LinearOracle
-- name    : OnlineConvexOpt_ProjectionFree_LinearOracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:41:08.777454+00:00
-- url     : https://prove2.me/theorems/e944261d-e93c-4b0a-98a5-065229045e84
-- title:
--   Linear-minimization oracle (the projection-free step)
-- statement:
--   Algorithm 25 line 3 and Algorithm 27 line 5 both replace a Euclidean projection with a
--   call to a **linear-minimization oracle**: given a direction (a gradient) `grad`, find a
--   point of `K` minimizing the linear functional $x \mapsto \langle \mathrm{grad}, x\rangle$
--   (Eq. (7.4), p. 126). `IsLinearMinimizer K grad v` says `v ∈ K` and `v` achieves this
--   minimum over `K`. This is the object the chapter's efficiency examples (matrix completion,
--   network routing, ranking, matroids) all exploit: computing this oracle is often far
--   cheaper than a Euclidean projection onto the same set.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 126, Eq. (7.4) (PDF p. 148)

import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.ProjectionFree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `v` solves the linear-minimization oracle over `K` in direction `grad` (Algorithm 25 line 3,
Algorithm 27 line 5, Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 126, PDF p. 148, Eq. (7.4)): `v ∈ K` minimizes the linear functional
`x ↦ ⟪grad, x⟫` over `K`. This is the "projection-free" step: a linear optimization oracle call
in place of a Euclidean projection. -/
def IsLinearMinimizer (K : Set E) (grad v : E) : Prop :=
  v ∈ K ∧ ∀ x ∈ K, ⟪grad, v⟫_ℝ ≤ ⟪grad, x⟫_ℝ

end OnlineConvexOpt.ProjectionFree


