-- Prove2me | solution 1 for ActuarialValuation.wholeLifeAssurancePV_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:01:58.482981+00:00
-- url     : https://prove2.me/submissions/2a366e45-3f98-4880-b231-67fb388d6605

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (i : ℝ) (hi : 0 < i) (ω : Ω)
    :
    0 < wholeLifeAssurancePV K (1 / (1 + i)) ω := by
  unfold wholeLifeAssurancePV
  have hden : 0 < 1 + i := by linarith
  have hv : 0 < (1 / (1 + i) : ℝ) := by positivity
  exact pow_pos hv _
