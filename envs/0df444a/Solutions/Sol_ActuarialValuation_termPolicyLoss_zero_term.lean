-- Prove2me | solution 1 for ActuarialValuation.termPolicyLoss_zero_term
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:00:08.460955+00:00
-- url     : https://prove2.me/submissions/96a3343d-6473-4b80-a472-c28969d2e9ab

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_termPolicyLossPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    (b π : ℝ)
    : termPolicyLossPV K v 0 b π ω = 0 := by
  simp [termPolicyLossPV, termAssurancePV, premiumDuePV, presentValue]
