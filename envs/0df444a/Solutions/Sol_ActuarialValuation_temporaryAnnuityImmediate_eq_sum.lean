-- Prove2me | solution 1 for ActuarialValuation.temporaryAnnuityImmediate_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:27:59.928781+00:00
-- url     : https://prove2.me/submissions/6f00b130-9bb5-42f1-9fa2-ef6467a9cbf6

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityImmediatePV
import Definitions.Def_actuarial_curtateSurvivalEvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    temporaryAnnuityImmediatePV K v n ω = ∑ k ∈ Finset.range n, v ^ (k + 1) * (curtateSurvivalEvent K (k + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω := by
  simp [temporaryAnnuityImmediatePV, presentValue]
