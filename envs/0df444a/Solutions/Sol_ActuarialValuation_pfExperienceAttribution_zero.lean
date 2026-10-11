-- Prove2me | solution 1 for ActuarialValuation.pfExperienceAttribution_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:13:25.056189+00:00
-- url     : https://prove2.me/submissions/85035463-68ae-4284-8706-897553145eca

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfExperienceAttribution
open ActuarialValuation

theorem solution(v : ℝ) : pfExperienceAttribution v v=0 := by
  simp [pfExperienceAttribution]
