-- Prove2me | solution 1 for ActuarialValuation.cm1ZeroReserveFloor_mono_next
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:26:41.894+00:00
-- url     : https://prove2.me/submissions/b68da150-2c47-47af-bafb-721e7e0036b2

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ZeroReserveFloor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c s g R₁ R₂ : ℝ) (hs : 0 ≤ s) (hg : 0 < g) (h : R₁ ≤ R₂) : cm1ZeroReserveFloor c s g R₁ ≤ cm1ZeroReserveFloor c s g R₂ := by
  unfold cm1ZeroReserveFloor
  have hm : s * R₁ ≤ s * R₂ := mul_le_mul_of_nonneg_left h hs
  have hfrac : (s * R₁ - c) / g ≤ (s * R₂ - c) / g := by
    apply (div_le_iff₀ hg).2
    have hd : (s * R₂ - c) / g * g = s * R₂ - c :=
      div_mul_cancel₀ _ (ne_of_gt hg)
    rw [hd]
    linarith
  exact max_le_max_left _ hfrac
