-- Prove2me | Definitions.Def_BinaryQueryLB_QueriesInBox
-- name    : BinaryQueryLB_QueriesInBox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:26.947958+00:00
-- url     : https://prove2.me/theorems/839e2c13-c599-4a0e-b03e-f2c88eabb6ee
-- title:
--   Queries of an algorithm lie in the box $X$
-- statement:
--   An algorithm **queries in $X$** if every query $(y,h)$ it can ask, after any answer history, has $y\in X=[-R,R]^d$. This is the requirement $y\in X$ of a local binary query.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.3, p.11

import Mathlib
import Definitions.Def_BinaryQueryLB_Algorithm
import Definitions.Def_BinaryQueryLB_Box

namespace BinaryQueryLB

/-- **The algorithm's queries are local binary queries.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.3, p.11: a local
binary query is a pair `(y, h)` with "a point `y ∈ X`".

`QueriesInBox d R A` says that every query the algorithm can ask, after any answer history, has its
point in the box `X = [−R, R]^d`. -/
def QueriesInBox (d : ℕ) (R : ℝ) (A : Algorithm d) : Prop :=
  ∀ (l : List Bool) (qr : LocalQuery d), A l = Sum.inl qr → qr.1 ∈ Box d R

end BinaryQueryLB


