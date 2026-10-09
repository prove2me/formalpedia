-- Prove2me | solution 1 for ActuarialValuation.wholeLifeImmediate_eq_due_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:26:50.917319+00:00
-- url     : https://prove2.me/submissions/15ae690c-bfe6-4cae-ac25-66318a261ebe

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (ω : Ω)
    :
    wholeLifeAnnuityImmediatePV K v ω = wholeLifeAnnuityDuePV K v ω - 1 := by
  unfold wholeLifeAnnuityDuePV wholeLifeAnnuityImmediatePV
  rw [Finset.sum_range_succ']
  simp only [pow_zero]
  ring
