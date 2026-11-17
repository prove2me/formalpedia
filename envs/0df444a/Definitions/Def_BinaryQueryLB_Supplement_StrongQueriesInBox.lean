-- Prove2me | Definitions.Def_BinaryQueryLB_Supplement_StrongQueriesInBox
-- name    : BinaryQueryLB_Supplement_StrongQueriesInBox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:51:50.615249+00:00
-- url     : https://prove2.me/theorems/29c33a4f-7644-4ada-8128-49e4ba1b232e
-- title:
--   The $O^*$-algorithm queries only points of $X$
-- statement:
--   An algorithm with $O^*$ **queries only points of $X$** if every query $(y,v)$ it can ask, after any history of answers, has $y\in X=[-R,R]^d$. The direction $v\in\mathbb R^d$ is unrestricted.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.2, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_Supplement_StrongAlgorithm
import Definitions.Def_BinaryQueryLB_Box

namespace BinaryQueryLB.Supplement

/-- **The O\*-algorithm queries only points of `X`.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.2, p.12: "The oracle `O∗` answers a query `(y, v)` with `y ∈ X` and `v ∈ R^d`".

`StrongQueriesInBox d R A` says that every query `(y, v)` the algorithm can ask, after any answer
history, has its point `y` in the box `X = [−R, R]^d`; the direction `v ∈ ℝ^d` is unrestricted. -/
def StrongQueriesInBox (d : ℕ) (R : ℝ) (A : StrongAlgorithm d) : Prop :=
  ∀ (l : List (ℝ × ℝ)) (q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)),
    A l = Sum.inl q → q.1 ∈ BinaryQueryLB.Box d R

end BinaryQueryLB.Supplement


