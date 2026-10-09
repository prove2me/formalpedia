-- Prove2me | solution 1 for ActuarialValuation.guaranteedImmediate_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:27:46.397539+00:00
-- url     : https://prove2.me/submissions/cbb97be8-a205-4961-bd3a-94e6332133d7

import Mathlib
import Definitions.Def_actuarial_guaranteedAnnuityImmediatePV
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    guaranteedAnnuityImmediatePV K v 0 ω = wholeLifeAnnuityImmediatePV K v ω := by
  simp [guaranteedAnnuityImmediatePV, wholeLifeAnnuityImmediatePV]

