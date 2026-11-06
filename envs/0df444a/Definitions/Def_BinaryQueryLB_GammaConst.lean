-- Prove2me | Definitions.Def_BinaryQueryLB_GammaConst
-- name    : BinaryQueryLB_GammaConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:53.828821+00:00
-- url     : https://prove2.me/theorems/d5f19f74-8ec5-430d-9231-3dd3d5ab64e5
-- title:
--   The constant $\Gamma=100$
-- statement:
--   The constant $\Gamma=100$ of the hard family.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.4, p.12

import Mathlib

namespace BinaryQueryLB

/-- **The constant `Γ = 100` (Definition 2.4).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.4, p.12. -/
noncomputable def GammaConst : ℝ := 100

end BinaryQueryLB


