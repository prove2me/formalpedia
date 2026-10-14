-- Prove2me | solution 1 for ActuarialValuation.frConditional_balance
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:02:05.791707+00:00
-- url     : https://prove2.me/submissions/3199834f-ff60-4f83-98b0-0048a183c258

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frConditionalUdd
import Definitions.Def_actuarial_frUddSurvival
open ActuarialValuation

theorem solution(q s t : ℝ) (hs : frUddSurvival q s ≠ 0) : frConditionalUdd q s t * frUddSurvival q s = frUddSurvival q (s+t) := by
  unfold frConditionalUdd
  exact div_mul_cancel₀ _ hs
