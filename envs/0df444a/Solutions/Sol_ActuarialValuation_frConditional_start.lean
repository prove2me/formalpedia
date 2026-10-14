-- Prove2me | solution 1 for ActuarialValuation.frConditional_start
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:22:14.164281+00:00
-- url     : https://prove2.me/submissions/70189e4d-c45f-4723-94ac-d30deb73cbd9

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frConditionalUdd
import Definitions.Def_actuarial_frUddSurvival
open ActuarialValuation

theorem solution(q s : ℝ) (hs : frUddSurvival q s ≠ 0) : frConditionalUdd q s 0 = 1 := by
  unfold frConditionalUdd
  rw [add_zero]
  exact div_self hs
