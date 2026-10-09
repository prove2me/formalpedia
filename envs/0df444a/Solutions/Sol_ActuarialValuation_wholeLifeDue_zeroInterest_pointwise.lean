-- Prove2me | solution 1 for ActuarialValuation.wholeLifeDue_zeroInterest_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:01:59.635626+00:00
-- url     : https://prove2.me/submissions/061a6e12-fbfe-4e79-97fc-893a4b8a969a

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (ω : Ω)
    :
    wholeLifeAnnuityDuePV K 1 ω = (K ω : ℝ) + 1 := by
  simp [wholeLifeAnnuityDuePV]
