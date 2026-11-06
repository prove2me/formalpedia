-- Prove2me | Definitions.Def_BinaryQueryLB_IsEpsOptimal
-- name    : BinaryQueryLB_IsEpsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:43:45.628726+00:00
-- url     : https://prove2.me/theorems/c386578f-4fa5-45d2-b10b-c4bcdd11ef07
-- title:
--   $\varepsilon$-optimal point
-- statement:
--   For $\varepsilon>0$, a point $\hat y\in X$ is **$\varepsilon$-optimal** for $f$ if $f(\hat y)-\min_X f\le\varepsilon$.
--
--   **Formalization Note** Stated as: $\hat y\in X$ and $f(\hat y)\le f(y)+\varepsilon$ for every $y\in X$. For the functions of $F(d,R,M)$, which are continuous on the compact box, the minimum is attained and the two forms agree; this form uses no infimum.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.1, p.11

import Mathlib
import Definitions.Def_BinaryQueryLB_Box

namespace BinaryQueryLB

/-- **ε-optimal point (Definition 2.1).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.1, p.11: "For `ε > 0`, a point
`ŷ ∈ X` is ε-optimal for `f` if `f(ŷ) − min_X f ≤ ε`."

**Formalization Note.** Written as `ŷ ∈ X` and `f ŷ ≤ f y + ε` for every `y ∈ X`. For every `f` of
the class `F(d, R, M)` (continuous on the compact box) the minimum over `X` is attained, and the
two forms are equivalent; this form avoids any `sInf` junk value. -/
def IsEpsOptimal (d : ℕ) (R : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (yh : EuclideanSpace ℝ (Fin d)) : Prop :=
  yh ∈ Box d R ∧ ∀ y ∈ Box d R, f yh ≤ f y + ε

end BinaryQueryLB


