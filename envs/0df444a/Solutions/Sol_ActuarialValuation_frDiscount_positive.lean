-- Prove2me | solution 1 for ActuarialValuation.frDiscount_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:33:04.876396+00:00
-- url     : https://prove2.me/submissions/48524b2f-2c5e-47a7-95fc-d8778bad3807

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDiscount
open ActuarialValuation

theorem solution(delta t : ℝ) : 0 < frDiscount delta t := by
  unfold frDiscount
  exact Real.exp_pos _
