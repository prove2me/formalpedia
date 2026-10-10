-- Prove2me | solution 1 for ActuarialValuation.retentionStopLossPremium_convex
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:04:59.286773+00:00
-- url     : https://prove2.me/submissions/1b83869a-32fb-494e-9ed6-96ecc29cf40c

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionStopLossPremium
import Definitions.Def_actuarial_retentionBlend
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w X : ℕ → ℝ) (B : ℕ) (a b θ : ℝ)
  (hw : ∀ s, 0 ≤ w s)
  (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
  retentionStopLossPremium w X B (retentionBlend a b θ) ≤
    (1 - θ) * retentionStopLossPremium w X B a +
      θ * retentionStopLossPremium w X B b := by
  have hpoint (x : ℝ) :
      retentionExcessPositive x (retentionBlend a b θ) ≤
      (1 - θ) * retentionExcessPositive x a +
        θ * retentionExcessPositive x b := by
    unfold retentionExcessPositive retentionBlend
    have ht : 0 ≤ 1 - θ := by linarith
    apply max_le
    · calc
        x - ((1 - θ) * a + θ * b) =
          (1 - θ) * (x - a) + θ * (x - b) := by ring
        _ ≤ (1 - θ) * max (x - a) 0 + θ * max (x - b) 0 :=
            add_le_add
              (mul_le_mul_of_nonneg_left (le_max_left _ _) ht)
              (mul_le_mul_of_nonneg_left (le_max_left _ _) hθ₀)
    · exact add_nonneg
        (mul_nonneg ht (le_max_right _ _))
        (mul_nonneg hθ₀ (le_max_right _ _))
  unfold retentionStopLossPremium
  calc
    (∑ s ∈ Finset.range (B + 1),
      w s * retentionExcessPositive (X s) (retentionBlend a b θ)) ≤
        ∑ s ∈ Finset.range (B + 1),
          ((1 - θ) * (w s * retentionExcessPositive (X s) a) +
            θ * (w s * retentionExcessPositive (X s) b)) := by
              apply Finset.sum_le_sum
              intro s hs
              have hmul := mul_le_mul_of_nonneg_left (hpoint (X s)) (hw s)
              nlinarith
    _ = (1 - θ) * (∑ s ∈ Finset.range (B + 1),
          w s * retentionExcessPositive (X s) a) +
        θ * (∑ s ∈ Finset.range (B + 1),
          w s * retentionExcessPositive (X s) b) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
