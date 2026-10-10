-- Prove2me | solution 1 for ActuarialValuation.retentionStopLossPremium_unit_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:04:50.078689+00:00
-- url     : https://prove2.me/submissions/4dfebbdc-48e9-4fb9-803e-696bf46e5799

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionStopLossPremium
import Definitions.Def_actuarial_retentionWeightTotal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w X : ℕ → ℝ) (B : ℕ) (a b : ℝ)
  (hw : ∀ s, 0 ≤ w s) (hW : retentionWeightTotal w B = 1)
  (hab : a ≤ b) :
  retentionStopLossPremium w X B a ≤
    retentionStopLossPremium w X B b + (b - a) := by
  have hmass : retentionStopLossPremium w X B a ≤
      retentionStopLossPremium w X B b +
        (b - a) * retentionWeightTotal w B := by
    unfold retentionStopLossPremium retentionWeightTotal
    calc
      (∑ s ∈ Finset.range (B + 1),
          w s * retentionExcessPositive (X s) a) ≤
        ∑ s ∈ Finset.range (B + 1),
          (w s * retentionExcessPositive (X s) b + (b - a) * w s) := by
            apply Finset.sum_le_sum
            intro s hs
            have hmax : retentionExcessPositive (X s) a ≤
                retentionExcessPositive (X s) b + (b - a) := by
              unfold retentionExcessPositive
              apply max_le
              · have hleft := le_max_left (X s - b) (0 : ℝ)
                linarith
              · have hright := le_max_right (X s - b) (0 : ℝ)
                linarith
            have hmul := mul_le_mul_of_nonneg_left hmax (hw s)
            nlinarith
      _ = (∑ s ∈ Finset.range (B + 1),
          w s * retentionExcessPositive (X s) b) +
        (b - a) * (∑ s ∈ Finset.range (B + 1), w s) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hW] at hmass
  nlinarith
