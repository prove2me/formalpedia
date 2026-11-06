-- Prove2me | Definitions.Def_BinaryQueryLB_hardFamily
-- name    : BinaryQueryLB_hardFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:48:29.129081+00:00
-- url     : https://prove2.me/theorems/7cd56077-1844-462b-9111-a86c9251d68f
-- title:
--   The hard family $\mathcal H$
-- statement:
--   The hard family is $\mathcal H=\{F_W:\ W\in\mathcal W\}$, with $m=\lfloor d/2\rfloor$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.4, p.12

import Mathlib
import Definitions.Def_BinaryQueryLB_FW__386b32
import Definitions.Def_BinaryQueryLB_Wset

namespace BinaryQueryLB

/-- **The hard family `ℋ = {F_W : W ∈ 𝒲}` (Definition 2.4).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.4, p.12. -/
def hardFamily (d : ℕ) (R M : ℝ) : Set (EuclideanSpace ℝ (Fin d) → ℝ) :=
  {f | ∃ W ∈ Wset (d / 2), FW d R M W = f}

end BinaryQueryLB


