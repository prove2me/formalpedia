-- Prove2me | solution 1 for ActuarialValuation.ulCOI_zero_mortality
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:56:30.813018+00:00
-- url     : https://prove2.me/submissions/73835f77-2d7c-4dba-8694-898ba9908d85

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulCOIAtStart
open ActuarialValuation

theorem solution(interest risk : ℝ) : ulCOIAtStart interest 0 risk = 0 := by
  simp [ulCOIAtStart]
