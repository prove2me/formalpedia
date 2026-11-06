-- Prove2me | Definitions.Def_BinaryQueryLB_StopsWith
-- name    : BinaryQueryLB_StopsWith
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:19.865275+00:00
-- url     : https://prove2.me/theorems/a7d994fd-2eef-4d0e-beac-490dca47fd3d
-- title:
--   The run stops after exactly $T$ queries with output $\hat y$
-- statement:
--   The algorithm $A$ **stops on $(f,G)$ after $T$ queries with output $\hat y$** if it asks a query at each of the steps $0,\dots,T-1$ of its run and, at step $T$, stops and outputs $\hat y$. Then $T$ is the number of queries it makes on $f$, repeated queries included.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.2, p.11

import Mathlib
import Definitions.Def_BinaryQueryLB_history

namespace BinaryQueryLB

/-- **The run stops after exactly `T` queries with output `ŷ`.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.2, p.11: "When it stops
after `T` queries, it outputs a point `ŷ` … every query counts, including repeated ones."

`StopsWith A G f T ŷ` says that on `(f, G)` the algorithm asks a query at each of the steps
`0, …, T − 1` and stops at step `T` with output `ŷ`; `T` is then the number of queries it makes
on `f`. -/
def StopsWith {d : ℕ} (A : Algorithm d) (G : Chart d) (f : EuclideanSpace ℝ (Fin d) → ℝ) (T : ℕ)
    (yh : EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ t < T, ∃ qr : LocalQuery d, A (history A G f t) = Sum.inl qr) ∧
    A (history A G f T) = Sum.inr yh

end BinaryQueryLB


