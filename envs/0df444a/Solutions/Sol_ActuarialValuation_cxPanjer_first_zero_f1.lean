-- Prove2me | solution 1 for ActuarialValuation.cxPanjer_first_zero_f1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:08:14.400063+00:00
-- url     : https://prove2.me/submissions/24220c37-0fe2-40d2-8886-5c718d58e384

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPanjerFirstRHS
open ActuarialValuation

theorem solution(a b g0 : ℝ) : cxPanjerFirstRHS a b 0 g0 = 0 := by
  simp [cxPanjerFirstRHS]
