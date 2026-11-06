-- Prove2me | Definitions.Def_BinaryQueryLB_xPart
-- name    : BinaryQueryLB_xPart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:43:50.698962+00:00
-- url     : https://prove2.me/theorems/5bcbd712-253e-495f-bf17-647cdad12c88
-- title:
--   The block $x$ of $q=(x,z)$
-- statement:
--   For $q=(x,z)\in\mathbb R^{2m}$, the first block $x\in\mathbb R^m$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.4, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_PtSpace

namespace BinaryQueryLB

/-- **The first block `x` of `q = (x, z)`.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.4, p.12. -/
def xPart {m : ℕ} (q : PtSpace m) : Fin m → ℝ := fun i => q (Sum.inl i)

end BinaryQueryLB


