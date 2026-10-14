-- Prove2me | solution 1 for ActuarialValuation.alterationPaidUpFraction_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:17:06.992982+00:00
-- url     : https://prove2.me/submissions/f03c9503-f75d-4061-934d-b000da96b2ab

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationPaidUpFraction
import Definitions.Def_actuarial_alterationPaidUpScaledValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (V B z : ℝ) (hB : B ≠ 0) (h : alterationPaidUpScaledValue z B = V) : z = alterationPaidUpFraction V B := by
  unfold alterationPaidUpScaledValue at h
  unfold alterationPaidUpFraction
  exact (eq_div_iff hB).2 h
