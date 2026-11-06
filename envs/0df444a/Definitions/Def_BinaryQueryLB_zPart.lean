-- Prove2me | Definitions.Def_BinaryQueryLB_zPart
-- name    : BinaryQueryLB_zPart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:43:53.370559+00:00
-- url     : https://prove2.me/theorems/cbbc2fd6-c582-40a4-8346-baddddac360a
-- title:
--   The block $z$ of $q=(x,z)$
-- statement:
--   For $q=(x,z)\in\mathbb R^{2m}$, the second block $z\in\mathbb R^m$, as a vector of the Euclidean space $\mathbb R^m$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.4, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_PtSpace

namespace BinaryQueryLB

/-- **The second block `z` of `q = (x, z)`, as a vector of ℝ^m.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.4, p.12. -/
noncomputable def zPart {m : ℕ} (q : PtSpace m) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun j => q (Sum.inr j))

end BinaryQueryLB


