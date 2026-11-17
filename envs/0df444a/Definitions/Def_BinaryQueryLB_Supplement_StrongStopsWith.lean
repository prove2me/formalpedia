-- Prove2me | Definitions.Def_BinaryQueryLB_Supplement_StrongStopsWith
-- name    : BinaryQueryLB_Supplement_StrongStopsWith
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:51:14.962619+00:00
-- url     : https://prove2.me/theorems/36936cd9-b350-4ee1-b205-15324579feb8
-- title:
--   A run with $O^*$ stops after exactly $T$ queries with output $\hat y$
-- statement:
--   The run of an algorithm $A$ with $O^*$ on $(f,G)$ **stops after exactly $T$ queries with output $\hat y$** if $A$ asks a query at each of the steps $0,\dots,T-1$ and, at step $T$, stops and outputs $\hat y$. Then $T$ is the number of queries $A$ makes on $f$ and $G$; repeated queries count.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.2, pp.11–12

import Mathlib
import Definitions.Def_BinaryQueryLB_Supplement_strongHistory

namespace BinaryQueryLB.Supplement

/-- **A run with O\* stops after exactly `T` queries with output `ŷ`.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.2, pp.11–12: when the algorithm "stops after `T` queries, it outputs a point
`ŷ` … every query counts, including repeated ones"; with `O∗` each query and the output are
functions of the previous real answers.

`StrongStopsWith A G f T ŷ` says that on `(f, G)` the algorithm asks a query at each of the steps
`0, …, T − 1` and stops at step `T` with output `ŷ`; `T` is then the number of queries it makes on
`(f, G)`. -/
def StrongStopsWith {d : ℕ} (A : StrongAlgorithm d) (G : BinaryQueryLB.Chart d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (T : ℕ) (yh : EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ t < T, ∃ q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      A (strongHistory A G f t) = Sum.inl q) ∧
    A (strongHistory A G f T) = Sum.inr yh

end BinaryQueryLB.Supplement


