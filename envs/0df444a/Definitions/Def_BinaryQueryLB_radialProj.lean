-- Prove2me | Definitions.Def_BinaryQueryLB_radialProj
-- name    : BinaryQueryLB_radialProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:20.444626+00:00
-- url     : https://prove2.me/theorems/85d7f941-deca-4c6d-9702-7a5f9ffb949a
-- title:
--   Radial projection $q^\circ=q/r(q)$
-- statement:
--   For $q\in\mathbb R^{2m}$ let $r(q)=\max\{1,\|q\|_2\}$ and
--   $$
--   q^\circ=q/r(q),
--   $$
--   the radial projection of $q$ onto the closed unit ball.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Lemma 2.9, p.14

import Mathlib
import Definitions.Def_BinaryQueryLB_PtSpace

namespace BinaryQueryLB

/-- **Radial projection `q° = q/r(q)` (Lemma 2.9).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Lemma 2.9, p.14: "For `q ∈ R^{2m}` write
`r(q) = max{1, ∥q∥₂}` and `q° = q/r(q)`." -/
noncomputable def radialProj {m : ℕ} (q : PtSpace m) : PtSpace m :=
  (max 1 ‖q‖)⁻¹ • q

end BinaryQueryLB


