-- Prove2me | solution 1 for ActuarialValuation.lcPeriodDeaths_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:54:15.144981+00:00
-- url     : https://prove2.me/submissions/1adf1113-ef40-479f-a948-e3557fff2206

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcPeriodDeaths
open ActuarialValuation

theorem solution(lives : ℝ) : lcPeriodDeaths lives 0 = 0 := by
  simp [lcPeriodDeaths]
