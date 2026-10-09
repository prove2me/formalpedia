-- Prove2me | solution 1 for ActuarialValuation.netLevelPremium_zero_benefit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:51:27.453154+00:00
-- url     : https://prove2.me/submissions/36deb271-9799-47da-a07d-498dcc74f484

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_netLevelPremium
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    : netLevelPremium P K v n 0 = 0 := by
  simp [netLevelPremium]
