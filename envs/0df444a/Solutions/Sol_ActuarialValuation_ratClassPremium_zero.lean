-- Prove2me | solution 1 for ActuarialValuation.ratClassPremium_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:51:17.792736+00:00
-- url     : https://prove2.me/submissions/40a9a149-1f28-4636-b2b9-809ce54d82d2

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratClassPremium
open ActuarialValuation

theorem solution(base rel : ℝ) : ratClassPremium 0 base rel = 0 := by
  simp [ratClassPremium]
