-- Prove2me | Definitions.Def_OnlineSaddlePoint_IsConvexConcaveOn
-- name    : OnlineSaddlePoint_IsConvexConcaveOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:14.86823+00:00
-- url     : https://prove2.me/theorems/ef976169-878d-41f9-9d2e-bfd48ef8f9b5
-- title:
--   Convex-concave function on $X\times Y$
-- statement:
--   A function $\mathcal L : X\times Y\to\mathbb R$ is **convex-concave** if $x\mapsto\mathcal L(x,y)$ is convex on $X$ for every fixed $y\in Y$, and $y\mapsto\mathcal L(x,y)$ is concave on $Y$ for every fixed $x\in X$.
--
--   This is the basic structural assumption of the online saddle point problem: the $x$-player minimizes a convex loss and the $y$-player maximizes a concave reward.
--
--   **Formalization Note** Mathlib's `ConvexOn ℝ X g` and `ConcaveOn ℝ Y h` include convexity of the sets $X$ and $Y$, so for nonempty $X$, $Y$ this predicate also asserts that both sets are convex.
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, §3, p.5

import Mathlib

namespace OnlineSaddlePoint

/-- **Convex-concave function.** Rivera Cardoso, Wang, Xu, arXiv:1806.08301v3, §3, p.5: "We say a
function `𝓛(x, y)` is convex-concave if it is convex in `x ∈ X`, for every fixed `y ∈ Y`, and
concave in `y ∈ Y`, for every fixed `x ∈ X`."

**Formalization Note.** Mathlib's `ConvexOn ℝ X g` includes convexity of the set `X`, and
`ConcaveOn ℝ Y h` convexity of `Y`. So whenever `Y` and `X` are nonempty, this predicate also
asserts that `X` and `Y` are convex, which the paper assumes throughout. -/
def IsConvexConcaveOn {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (X : Set E) (Y : Set F) (f : E → F → ℝ) : Prop :=
  (∀ y ∈ Y, ConvexOn ℝ X (fun x => f x y)) ∧ (∀ x ∈ X, ConcaveOn ℝ Y (fun y => f x y))

end OnlineSaddlePoint


