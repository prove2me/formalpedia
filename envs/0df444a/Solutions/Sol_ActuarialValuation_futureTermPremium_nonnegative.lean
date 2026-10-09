-- Prove2me | solution 1 for ActuarialValuation.futureTermPremium_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:53:42.537788+00:00
-- url     : https://prove2.me/submissions/96abee6b-6db5-4467-ab9b-ccbac0165c40

import Mathlib
import Definitions.Def_actuarial_futureTermPremiumPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (ω : Ω)
    (hv : 0 ≤ v)
    :
    0 ≤ futureTermPremiumPV K v n t ω := by
  unfold futureTermPremiumPV
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact pow_nonneg hv _
  · exact le_refl _
