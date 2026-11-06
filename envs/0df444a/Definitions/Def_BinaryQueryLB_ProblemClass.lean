-- Prove2me | Definitions.Def_BinaryQueryLB_ProblemClass
-- name    : BinaryQueryLB_ProblemClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:43:45.895071+00:00
-- url     : https://prove2.me/theorems/ba442694-c9da-4024-9061-93be752da5bd
-- title:
--   Problem class $F(d,R,M)$
-- statement:
--   Let $X=[-R,R]^d$. The class $F(d,R,M)$ consists of the convex functions $f:\mathbb R^d\to\mathbb R$ with $f(0)=0$ and
--   $$
--   |f(y)-f(y')|\le M\,\|y-y'\|_\infty\qquad\text{for all }y,y'\in X .
--   $$
--
--   This is the class of unconstrained convex problems on the box for which the paper proves its query lower bound.
--
--   **Formalization Note** Convexity is on all of $\mathbb R^d$; the Lipschitz condition, in the maximum norm, only on $X$. The standing assumptions $d\ge2$, $R,M>0$ are hypotheses of the theorems.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.1, p.11

import Mathlib
import Definitions.Def_BinaryQueryLB_supNorm
import Definitions.Def_BinaryQueryLB_Box

namespace BinaryQueryLB

/-- **Problem class `F(d, R, M)` (Definition 2.1).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.1, p.11: "The class
`F(d, R, M)` consists of the convex functions `f` from `R^d` to `R` with `f(0) = 0` and
`|f(y) − f(y′)| ≤ M∥y − y′∥∞` for all `y, y′ ∈ X`."

**Formalization Note.** Convexity is `ConvexOn ℝ Set.univ f` on all of ℝ^d; the Lipschitz
condition uses the maximum norm `supNorm` and is required only on the box `X = Box d R`. The
standing assumptions `d ≥ 2`, `R, M > 0` of the definition are hypotheses of every theorem. -/
def ProblemClass (d : ℕ) (R M : ℝ) : Set (EuclideanSpace ℝ (Fin d) → ℝ) :=
  {f | ConvexOn ℝ Set.univ f ∧ f 0 = 0 ∧
    ∀ y ∈ Box d R, ∀ y' ∈ Box d R, |f y - f y'| ≤ M * supNorm (y - y')}

end BinaryQueryLB


