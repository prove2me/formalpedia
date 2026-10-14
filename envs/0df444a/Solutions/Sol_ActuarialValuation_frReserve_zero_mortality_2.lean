-- Prove2me | solution 2 for ActuarialValuation.frReserve_zero_mortality
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:33.613638+00:00
-- url     : https://prove2.me/submissions/a29a162b-2a4b-437a-a01c-3cdc4ec7e4d2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frFractionalReserve
open ActuarialValuation

theorem solution (assets premium benefit s growth endDiscount : ℝ) : frFractionalReserve assets premium benefit 0 s growth endDiscount = (assets+premium)*growth := by
  simp [frFractionalReserve, frUddSurvival]
