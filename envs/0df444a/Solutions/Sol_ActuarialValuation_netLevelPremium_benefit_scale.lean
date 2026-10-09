-- Prove2me | solution 1 for ActuarialValuation.netLevelPremium_benefit_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:52:44.769188+00:00
-- url     : https://prove2.me/submissions/7ee1f28f-1304-4f6e-ae6e-ffc23a9bafae

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
    (v : ℝ) (n : ℕ) (b c : ℝ)
    : netLevelPremium P K v n (c * b) =
        c * netLevelPremium P K v n b := by
  unfold netLevelPremium
  ring
