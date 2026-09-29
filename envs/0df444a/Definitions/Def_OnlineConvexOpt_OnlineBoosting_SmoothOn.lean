-- Prove2me | Definitions.Def_OnlineConvexOpt_OnlineBoosting_SmoothOn
-- name    : OnlineConvexOpt_OnlineBoosting_SmoothOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:48:34.401227+00:00
-- url     : https://prove2.me/theorems/a59b7a85-4baf-4467-8863-cc86e849f035
-- title:
--   β-smoothness (redeclared)
-- statement:
--   `f` is `β`-smooth on `K` with gradient map `g` (p. 18, reused p. 201: "`f̂_t` is `dG/δ`-
--   smooth"): for every `x, y ∈ K`, $f(y) \le f(x) + \langle g(x),y-x\rangle +
--   \frac\beta2\|y-x\|^2$. Redeclared under this chapter's sub-namespace, matching the
--   convention already used in Chunks 07 and 10 (Chapter II is not yet published).
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 18 (PDF p. 40)

import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.OnlineBoosting

/-- `f` is `β`-smooth on `K` with gradient map `g` (Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 18, PDF p. 40; used again p. 201, PDF p. 223,
"`f̂_t` is `dG/δ`-smooth"): for every `x y ∈ K`,
`f y ≤ f x + ⟪g x, y - x⟫_ℝ + (β / 2) * ‖y - x‖ ^ 2`. Redeclared here (not imported) since
Chapter II's own smoothness is not yet a published series definition. -/
def SmoothOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (f : E → ℝ) (g : E → E) (β : ℝ) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, f y ≤ f x + ⟪g x, y - x⟫_ℝ + (β / 2) * ‖y - x‖ ^ 2

end OnlineConvexOpt.OnlineBoosting


