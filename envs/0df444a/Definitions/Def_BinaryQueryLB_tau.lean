-- Prove2me | Definitions.Def_BinaryQueryLB_tau
-- name    : BinaryQueryLB_tau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:43:55.144392+00:00
-- url     : https://prove2.me/theorems/3f4e8c75-e564-4ab4-ab82-3d3f648e0143
-- title:
--   The radius $\tau=a/(\Gamma\sqrt m)$
-- statement:
--   For $m\ge1$, the radius of the row sets of the hard family is $\tau=\dfrac{a}{\Gamma\sqrt m}$, with $a=\tfrac12$ and $\Gamma=100$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.4, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_aConst
import Definitions.Def_BinaryQueryLB_GammaConst

namespace BinaryQueryLB

/-- **The radius `τ = a/(Γ√m)` (Definition 2.4).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.4, p.12. -/
noncomputable def tau (m : ℕ) : ℝ := aConst / (GammaConst * Real.sqrt m)

end BinaryQueryLB


