-- Prove2me | solution 1 for ActuarialValuation.irCountUltimate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:03:56.463379+00:00
-- url     : https://prove2.me/submissions/a5ebd3d9-401e-4567-af64-37f1f02c271e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irClaimCountUltimate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (count factor : ℝ) (hc : 0≤count) (hf : 0≤factor) : 0≤irClaimCountUltimate count factor := by
  unfold irClaimCountUltimate
  exact mul_nonneg hc hf
