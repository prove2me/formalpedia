-- Prove2me | solution 1 for ActuarialValuation.coRectangle_zero_height
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:40:04.94546+00:00
-- url     : https://prove2.me/submissions/f032bf9b-8d98-4117-911e-dc179504540a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coRectangle
open ActuarialValuation

theorem solution(C : ℝ → ℝ → ℝ) (u1 u2 v : ℝ) : coRectangle C u1 u2 v v=0 := by
  unfold coRectangle
  ring
