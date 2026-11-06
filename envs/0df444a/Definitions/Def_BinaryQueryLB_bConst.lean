-- Prove2me | Definitions.Def_BinaryQueryLB_bConst
-- name    : BinaryQueryLB_bConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:09.43364+00:00
-- url     : https://prove2.me/theorems/27851508-618f-4e9c-883b-b976f143c748
-- title:
--   The radial coefficient $b=2a/\sqrt m$
-- statement:
--   For $m\ge1$, the coefficient of the radial term of the hard family is $b=\dfrac{2a}{\sqrt m}$ with $a=\tfrac12$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.4, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_aConst

namespace BinaryQueryLB

/-- **The radial coefficient `b = 2a/√m` (Definition 2.4).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.4, p.12. -/
noncomputable def bConst (m : ℕ) : ℝ := 2 * aConst / Real.sqrt m

end BinaryQueryLB


