-- Prove2me | solution 1 for ActuarialValuation.panjerFrequencyPremium_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:44:53.055917+00:00
-- url     : https://prove2.me/submissions/9bfa6ddf-cb4f-436c-9bc7-4cec663e6ae0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerFrequencyPremium
open ActuarialValuation

theorem solution(mean : ℝ) : panjerFrequencyPremium 0 mean = 0 := by
  simp [panjerFrequencyPremium]
