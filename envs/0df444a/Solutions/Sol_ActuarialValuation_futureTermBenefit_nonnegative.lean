-- Prove2me | solution 1 for ActuarialValuation.futureTermBenefit_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:53:34.277162+00:00
-- url     : https://prove2.me/submissions/ec675616-2046-4bc8-be32-b4219a2bb772

import Mathlib
import Definitions.Def_actuarial_futureTermBenefitPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (ω : Ω)
    (hv : 0 ≤ v)
    :
    0 ≤ futureTermBenefitPV K v n t ω := by
  unfold futureTermBenefitPV
  split_ifs
  · exact pow_nonneg hv _
  · exact le_refl _
