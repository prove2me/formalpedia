-- Prove2me | solution 1 for ActuarialValuation.temporaryAnnuityDue_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:27:57.553449+00:00
-- url     : https://prove2.me/submissions/52e36243-d7be-49ae-9999-78554d58673a

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityDuePV
import Definitions.Def_actuarial_curtateSurvivalEvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    temporaryAnnuityDuePV K v n ω = ∑ k ∈ Finset.range n, v ^ k * (curtateSurvivalEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω := by
  simp [temporaryAnnuityDuePV, presentValue]
