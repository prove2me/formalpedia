-- Prove2me | Definitions.Def_GrothendieckLB_IsTernaryFn
-- name    : GrothendieckLB_IsTernaryFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:27.424377+00:00
-- url     : https://prove2.me/theorems/e873dea0-e63b-48a9-953f-ab3747a71d1c
-- title:
--   Measurable ternary function
-- statement:
--   A function $F$ on a measurable space is **ternary** if it is measurable and takes values in $\{-1,0,1\}$. The agreement part $h$, the disagreement part $k$ and their one-dimensional fibers $u_t$ are ternary.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.1, p.32; Section 8.4, p.36

import Mathlib

namespace GrothendieckLB

/-- A measurable ternary function `F : α → {-1, 0, 1}` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.1, p.32; Section 8.4, p.36). -/
def IsTernaryFn {α : Type*} [MeasurableSpace α] (F : α → ℝ) : Prop :=
  Measurable F ∧ ∀ x, F x = 1 ∨ F x = 0 ∨ F x = -1

end GrothendieckLB


