-- Prove2me | solution 1 for ActuarialValuation.ulSurrenderValue_at_zero_charge
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:59:25.501036+00:00
-- url     : https://prove2.me/submissions/e4464862-f7ee-4d5f-91f3-2d94b598db2f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulSurrenderValue
open ActuarialValuation

theorem solution(fund : ℝ) (hf : 0 ≤ fund) : ulSurrenderValue fund 0=fund := by
  unfold ulSurrenderValue
  simp only [sub_zero]
  exact max_eq_right hf
