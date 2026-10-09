-- Prove2me | solution 1 for ActuarialValuation.premiumDuePV_zero_term
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:51:11.712999+00:00
-- url     : https://prove2.me/submissions/ff995437-84bf-4288-9172-7fbb61acf341

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_premiumDuePV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    : premiumDuePV K v 0 ω = 0 := by
  simp [premiumDuePV]
