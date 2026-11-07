-- Prove2me | solution 2 for ActuarialValuation.negBinClaimFrequency_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @hacv16
-- created : 2026-11-06T17:40:41.555955+00:00
-- url     : https://prove2.me/submissions/2f987b8d-25be-4c6d-b9f3-50b8f444e1e4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinGammaPredictive
import Definitions.Def_actuarial_negBinGammaProbability
import Definitions.Def_actuarial_negBinCountMean
import Definitions.Def_actuarial_negBinCountVariance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
open ActuarialValuation
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
theorem solution (r n : ℕ) (b : ℝ)
  (hr : 0 < r) (hb : 0 < b) :
  ((n + 1 : ℝ) * negBinGammaPredictive r b (n + 1) =
    ((n + r : ℕ) : ℝ) * negBinGammaProbability b *
       negBinGammaPredictive r b n) ∧
  (negBinCountMean r (negBinGammaProbability b) = (r : ℝ) / b) ∧
  (negBinCountVariance r (negBinGammaProbability b) =
    (r : ℝ) / b + (r : ℝ) / b ^ 2) ∧
  (0 ≤ negBinGammaPredictive r b n) := (
by
  have NB_moments_nonneg : (∀ (r n : ℕ) (b : ℝ), 0 < b → (ActuarialValuation.negBinCountMean r (ActuarialValuation.negBinGammaProbability b) = (r : ℝ) / b) ∧ (ActuarialValuation.negBinCountVariance r (ActuarialValuation.negBinGammaProbability b) = (r : ℝ) / b + (r : ℝ) / b ^ 2) ∧ (0 ≤ ActuarialValuation.negBinGammaPredictive r b n)) := (
by
  intro r n b hb
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hb1pos : 0 < b + 1 := by linarith
  have hb10 : b + 1 ≠ 0 := ne_of_gt hb1pos
  have hsub : 1 - 1 / (b + 1) = b / (b + 1) := by
    field_simp [hb10]
    <;> ring
  constructor
  · dsimp [ActuarialValuation.negBinCountMean, ActuarialValuation.negBinGammaProbability]
    rw [hsub]
    field_simp [hb0, hb10]
    <;> ring
  · constructor
    · dsimp [ActuarialValuation.negBinCountVariance, ActuarialValuation.negBinGammaProbability]
      rw [hsub]
      field_simp [hb0, hb10]
      <;> ring
    · unfold ActuarialValuation.negBinGammaPredictive ActuarialValuation.negBinCountMass ActuarialValuation.negBinGammaProbability
      rw [hsub]
      positivity
)
  have Lrec : (∀ (r n : ℕ) (p : ℝ), 0 < r → ((n + 1 : ℝ) * ActuarialValuation.negBinCountMass r p (n + 1) = ((n + r : ℕ) : ℝ) * p * ActuarialValuation.negBinCountMass r p n)) := (
by
  have NB_moments_nonneg : (∀ (r n : ℕ) (b : ℝ), 0 < b → (ActuarialValuation.negBinCountMean r (ActuarialValuation.negBinGammaProbability b) = (r : ℝ) / b) ∧ (ActuarialValuation.negBinCountVariance r (ActuarialValuation.negBinGammaProbability b) = (r : ℝ) / b + (r : ℝ) / b ^ 2) ∧ (0 ≤ ActuarialValuation.negBinGammaPredictive r b n)) := (
by
  intro r n b hb
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hb1pos : 0 < b + 1 := by linarith
  have hb10 : b + 1 ≠ 0 := ne_of_gt hb1pos
  have hsub : 1 - 1 / (b + 1) = b / (b + 1) := by
    field_simp [hb10]
    <;> ring
  constructor
  · dsimp [ActuarialValuation.negBinCountMean, ActuarialValuation.negBinGammaProbability]
    rw [hsub]
    field_simp [hb0, hb10]
    <;> ring
  · constructor
    · dsimp [ActuarialValuation.negBinCountVariance, ActuarialValuation.negBinGammaProbability]
      rw [hsub]
      field_simp [hb0, hb10]
      <;> ring
    · unfold ActuarialValuation.negBinGammaPredictive ActuarialValuation.negBinCountMass ActuarialValuation.negBinGammaProbability
      rw [hsub]
      positivity
)
  exact (
by
  intro r n p hr
  have hidx : n + r - 1 + 1 = n + r := by omega
  have hidx' : n + 1 + r - 1 = n + r := by omega
  have hc : (n + 1) * Nat.choose (n + 1 + r - 1) (n + 1) =
      (n + r) * Nat.choose (n + r - 1) n := by
    simpa only [hidx, hidx', Nat.mul_comm] using
      (Nat.add_one_mul_choose_eq (n + r - 1) n).symm
  have hcR : (n + 1 : ℝ) * (Nat.choose (n + 1 + r - 1) (n + 1) : ℝ) =
      ((n + r : ℕ) : ℝ) * (Nat.choose (n + r - 1) n : ℝ) := by
    exact_mod_cast hc
  unfold ActuarialValuation.negBinCountMass
  rw [pow_succ]
  linear_combination (1 - p) ^ r * p ^ n * p * hcR
)
)
  exact (
by
  refine ⟨?_, NB_moments_nonneg r n b hb⟩
  simpa only [ActuarialValuation.negBinGammaPredictive] using
    Lrec r n (ActuarialValuation.negBinGammaProbability b) hr
)
)
