-- Prove2me | solution 2 for ActuarialValuation.frReserve_annual
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:33.473658+00:00
-- url     : https://prove2.me/submissions/3ae25831-8ee9-4507-aad1-6eb8b7bc30f3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frFractionalReserve
import Definitions.Def_actuarial_frAnnualReserve
open ActuarialValuation

theorem solution (assets premium benefit q growth : ℝ) : frFractionalReserve assets premium benefit q 1 growth 1 = frAnnualReserve assets premium benefit q growth := by
  simp [frAnnualReserve, frFractionalReserve, frUddSurvival]
