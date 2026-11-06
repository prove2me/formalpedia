-- Prove2me | Definitions.Def_BinaryQueryLB_aConst
-- name    : BinaryQueryLB_aConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:59.959819+00:00
-- url     : https://prove2.me/theorems/fe391f19-402e-4675-a83c-5dcd3e1d707d
-- title:
--   The constant $a=1/2$
-- statement:
--   The constant $a=\tfrac12$ of the hard family.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.4, p.12

import Mathlib

namespace BinaryQueryLB

/-- **The constant `a = 1/2` (Definition 2.4).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.4, p.12. -/
noncomputable def aConst : ℝ := 1 / 2

end BinaryQueryLB


