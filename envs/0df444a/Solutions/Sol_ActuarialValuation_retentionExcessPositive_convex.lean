-- Prove2me | solution 1 for ActuarialValuation.retentionExcessPositive_convex
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:56:52.487269+00:00
-- url     : https://prove2.me/submissions/ffd5ed31-78de-49f2-8f0e-789084dfa718

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionExcessPositive
import Definitions.Def_actuarial_retentionBlend
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (x a b θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
  retentionExcessPositive x (retentionBlend a b θ) ≤
    (1 - θ) * retentionExcessPositive x a +
      θ * retentionExcessPositive x b := by
  unfold retentionExcessPositive retentionBlend
  have hθ' : 0 ≤ 1 - θ := by linarith
  apply max_le
  · calc
      x - ((1 - θ) * a + θ * b) =
          (1 - θ) * (x - a) + θ * (x - b) := by ring
      _ ≤ (1 - θ) * max (x - a) 0 + θ * max (x - b) 0 :=
        add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hθ')
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hθ₀)
  · exact add_nonneg
      (mul_nonneg hθ' (le_max_right _ _))
      (mul_nonneg hθ₀ (le_max_right _ _))
