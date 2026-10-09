-- Prove2me | solution 1 for ActuarialValuation.guaranteedDue_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:27:40.602441+00:00
-- url     : https://prove2.me/submissions/e8c1adf1-bfa6-4d67-9d98-2fe6e9d6b4db

import Mathlib
import Definitions.Def_actuarial_guaranteedAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    guaranteedAnnuityDuePV K v 0 ω = wholeLifeAnnuityDuePV K v ω := by
  simp [guaranteedAnnuityDuePV, wholeLifeAnnuityDuePV]

