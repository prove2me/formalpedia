-- Prove2me | solution 1 for ActuarialValuation.ratPurePremium_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:04:23.399907+00:00
-- url     : https://prove2.me/submissions/b1178250-4f71-4730-9b92-2b72c635b3e8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratPurePremium
open ActuarialValuation

theorem solution(exposure : ℝ) : ratPurePremium 0 exposure = 0 := by
  simp [ratPurePremium]
