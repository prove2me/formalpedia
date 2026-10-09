-- Prove2me | solution 1 for ActuarialValuation.netLevelPremium_zero_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:57:08.155156+00:00
-- url     : https://prove2.me/submissions/686c0e20-0624-4f2f-a0fd-e578f82d6635

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
    (v : ℝ) (n : ℕ) (b : ℝ) (hn : 0 < n)
    : netLevelPremium P K 0 n b = 0 := by
  unfold netLevelPremium
  have hzero : (fun ω : Ω => termAssurancePV K 0 n ω) = 0 := by
    funext ω
    simp [termAssurancePV, presentValue]
  simp [hzero]
