-- Prove2me | Definitions.Def_AdditiveConvexity_SlopeLEInCoord
-- name    : AdditiveConvexity_SlopeLEInCoord
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:25.182573+00:00
-- url     : https://prove2.me/theorems/26aca0a8-0367-45bb-8a19-101ef434ac3e
-- title:
--   Slope bound $a$ in a coordinate on $V$
-- statement:
--   A function $f$ has **slope bound $a$ in coordinate $m$ on $V$** if
--   $$
--   f(x')-f(x)\le a\,(x'_m-x_m)
--   $$
--   for all $x,x'\in V$ that agree off coordinate $m$ and satisfy $x_m\le x'_m$. No sign is imposed on $a$.
--
--   This is the form taken here by the bound $\partial f(x)/\partial x_m\le a$ of Theorem 1. For a differentiable function the derivative bound gives the slope bound by the mean value theorem on a section of $V$, and a slope bound forces every existing partial derivative to be at most $a$.
--
--   **Formalization Note** The paper's functions are only assumed convex, and the value function need not be differentiable, so the bound is stated on difference quotients.
-- source:
--   Gong–Wang, Preservation of Additive Convexity, SSRN 3217007 (accepted manuscript), Theorem 1, p.4 (PDF p.4)

import Mathlib

namespace AdditiveConvexity

/-- Slope bound `a` for `f` in coordinate `m` on `V`, the reading of `∂f(x)/∂x_m ≤ a` for all
`x ∈ V` in Gong–Wang, Preservation of Additive Convexity, SSRN 3217007 (accepted manuscript),
Theorem 1, p.4 (PDF p.4).

**Formalization Note.** Theorem 1 assumes convexity only and its `g` need not be differentiable,
so the bound is stated on difference quotients: for `x, x' ∈ V` agreeing off `m` with
`x m ≤ x' m`, `f x' - f x ≤ a * (x' m - x m)`. No sign is imposed on `a`. -/
def SlopeLEInCoord {ι : Type*} (V : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ) (m : ι) (a : ℝ) : Prop :=
  ∀ x ∈ V, ∀ x' ∈ V, (∀ i, i ≠ m → x i = x' i) → x m ≤ x' m → f x' - f x ≤ a * (x' m - x m)

end AdditiveConvexity


