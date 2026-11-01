-- Prove2me | Definitions.Def_AdditiveConvexity_IncreasingInCoord
-- name    : AdditiveConvexity_IncreasingInCoord
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:22.374147+00:00
-- url     : https://prove2.me/theorems/87ba0815-5489-4c50-a67b-c8ad82da157f
-- title:
--   $f$ increasing in a coordinate on $V$
-- statement:
--   A function $f$ is **increasing in coordinate $m$ on $V$** if $f(x)\le f(x')$ for all $x,x'\in V$ that agree off coordinate $m$ and satisfy $x_m\le x'_m$.
--
--   The paper uses "increasing" in the non-strict sense (p.3).
--
--   **Formalization Note** Only pairs of points of $V$ are compared, so the values of $f$ off $V$ do not matter.
-- source:
--   Gong–Wang, Preservation of Additive Convexity, SSRN 3217007 (accepted manuscript), p.3 (PDF p.3, convention) and Theorem 1, p.4 (PDF p.4)

import Mathlib

namespace AdditiveConvexity

/-- `f` is increasing in coordinate `m` on `V`: Gong–Wang, Preservation of Additive Convexity,
SSRN 3217007 (accepted manuscript), p.3 (PDF p.3; "increasing" is non-decreasing) and Theorem 1,
p.4 (PDF p.4).

**Formalization Note.** Only pairs of points of `V` that agree off coordinate `m` are compared. -/
def IncreasingInCoord {ι : Type*} (V : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ) (m : ι) : Prop :=
  ∀ x ∈ V, ∀ x' ∈ V, (∀ i, i ≠ m → x i = x' i) → x m ≤ x' m → f x ≤ f x'

end AdditiveConvexity


