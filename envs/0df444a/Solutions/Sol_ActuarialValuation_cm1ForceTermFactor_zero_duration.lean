-- Prove2me | solution 1 for ActuarialValuation.cm1ForceTermFactor_zero_duration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:29:16.895967+00:00
-- url     : https://prove2.me/submissions/26edc29f-b658-4a39-80c5-39874fa1cd96

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ForceTermFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ : ℝ) : cm1ForceTermFactor δ μ 0 0 = 0 := by
  simp [cm1ForceTermFactor]
