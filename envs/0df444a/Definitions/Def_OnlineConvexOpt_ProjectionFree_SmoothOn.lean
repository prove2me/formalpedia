-- Prove2me | Definitions.Def_OnlineConvexOpt_ProjectionFree_SmoothOn
-- name    : OnlineConvexOpt_ProjectionFree_SmoothOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:41:30.573984+00:00
-- url     : https://prove2.me/theorems/00b6da42-fd3b-4f5c-ac3c-0c65a45046c3
-- title:
--   β-smoothness (redeclared)
-- statement:
--   `f` is `β`-smooth on `K` with gradient map `g` when, for every `x, y ∈ K`,
--   $f(y) \le f(x) + \langle g(x), y-x\rangle + \frac{\beta}{2}\|y-x\|^2$ (p. 18, restated in
--   this chapter, e.g. p. 134, "the functions $F_t$ are 1-smooth"). Redeclared under this
--   chapter's sub-namespace rather than imported, since Chapter II's own `SmoothOn` is not yet
--   a published series definition (see `MODERATION_NOTES.md`).
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 18 (PDF p. 40); p. 134 (PDF p. 156)

import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.ProjectionFree

/-- `f` is `β`-smooth on `K` with gradient map `g`: for every `x y ∈ K`,
`f y ≤ f x + ⟪g x, y - x⟫_ℝ + (β / 2) * ‖y - x‖ ^ 2` (Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 18, PDF p. 40; used again in this chapter, e.g.
p. 127 Theorem 7.1, p. 134 "the functions `Ft` are 1-smooth"). Redeclared here (not imported)
since Chapter II's `ConvexBasics.SmoothOn` is not yet a published series definition; see
`MODERATION_NOTES.md`. -/
def SmoothOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (f : E → ℝ) (g : E → E) (β : ℝ) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, f y ≤ f x + ⟪g x, y - x⟫_ℝ + (β / 2) * ‖y - x‖ ^ 2

end OnlineConvexOpt.ProjectionFree


