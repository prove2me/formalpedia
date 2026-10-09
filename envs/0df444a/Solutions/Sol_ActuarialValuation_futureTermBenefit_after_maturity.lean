-- Prove2me | solution 1 for ActuarialValuation.futureTermBenefit_after_maturity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:53:09.210302+00:00
-- url     : https://prove2.me/submissions/bc5e28f1-cb76-4d29-9924-9882a31b47ad

import Mathlib
import Definitions.Def_actuarial_futureTermBenefitPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (ω : Ω)
    (ht : n ≤ t)
    :
    futureTermBenefitPV K v n t ω = 0 := by
  unfold futureTermBenefitPV
  split_ifs with h
  · omega
  · rfl
