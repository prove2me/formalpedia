-- Prove2me | solution 1 for ActuarialValuation.negBinClaimFrequency_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:17:58.909322+00:00
-- url     : https://prove2.me/submissions/b2b9df98-af6a-4246-a357-09083d1b95c0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinGammaPredictive
import Definitions.Def_actuarial_negBinGammaProbability
import Definitions.Def_actuarial_negBinCountMean
import Definitions.Def_actuarial_negBinCountVariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (r n : ℕ) (b : ℝ)
  (hr : 0 < r) (hb : 0 < b) :
  ((n + 1 : ℝ) * negBinGammaPredictive r b (n + 1) =
    ((n + r : ℕ) : ℝ) * negBinGammaProbability b *
       negBinGammaPredictive r b n) ∧
  (negBinCountMean r (negBinGammaProbability b) = (r : ℝ) / b) ∧
  (negBinCountVariance r (negBinGammaProbability b) =
    (r : ℝ) / b + (r : ℝ) / b ^ 2) ∧
  (0 ≤ negBinGammaPredictive r b n) := by
  have hcoef : (n + 1) * Nat.choose (n + r) (n + 1) =
      (n + r) * Nat.choose (n + r - 1) n := by
    cases n with
    | zero => simp [Nat.choose_one_right]
    | succ k =>
      have htop1 : k + r + 1 - (k + 1) = r := by omega
      have htop2 : k + r - k = r := by omega
      have h1 := Nat.choose_succ_right_eq (k + r + 1) (k + 1)
      have h2 := Nat.choose_succ_right_eq (k + r) k
      have hp := Nat.choose_succ_succ (k + r) k
      rw [htop1] at h1
      rw [htop2] at h2
      have hp' : Nat.choose (k + r + 1) (k + 1) =
          Nat.choose (k + r) k + Nat.choose (k + r) (k + 1) := by
        simpa [Nat.add_assoc] using hp
      have hs : (k + 2) * Nat.choose (k + r + 1) (k + 2) =
          (k + 1 + r) * Nat.choose (k + r) (k + 1) := by
        calc
          (k + 2) * Nat.choose (k + r + 1) (k + 2) =
              Nat.choose (k + r + 1) (k + 2) * (k + 2) := Nat.mul_comm _ _
          _ = Nat.choose (k + r + 1) (k + 1) * r := h1
          _ = (Nat.choose (k + r) k + Nat.choose (k + r) (k + 1)) * r := by rw [hp']
          _ = (k + 1 + r) * Nat.choose (k + r) (k + 1) := by nlinarith
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hcoefR : (n + 1 : ℝ) * (Nat.choose (n + r) (n + 1) : ℝ) =
      ((n + r : ℕ) : ℝ) * (Nat.choose (n + r - 1) n : ℝ) := by
    exact_mod_cast hcoef
  have htop : (n + 1) + r - 1 = n + r := by omega
  have hrec :
      (n + 1 : ℝ) * negBinCountMass r (negBinGammaProbability b) (n + 1) =
        ((n + r : ℕ) : ℝ) * negBinGammaProbability b *
          negBinCountMass r (negBinGammaProbability b) n := by
    unfold negBinCountMass
    rw [htop, pow_succ]
    calc
      _ = ((n + 1 : ℝ) * (Nat.choose (n + r) (n + 1) : ℝ)) *
          negBinGammaProbability b * (1 - negBinGammaProbability b) ^ r *
          negBinGammaProbability b ^ n := by ring
      _ = (((n + r : ℕ) : ℝ) * (Nat.choose (n + r - 1) n : ℝ)) *
          negBinGammaProbability b * (1 - negBinGammaProbability b) ^ r *
          negBinGammaProbability b ^ n := by rw [hcoefR]
      _ = ((n + r : ℕ) : ℝ) * negBinGammaProbability b *
          ((Nat.choose (n + r - 1) n : ℝ) *
            (1 - negBinGammaProbability b) ^ r *
            negBinGammaProbability b ^ n) := by ring
  have hmean :
      negBinCountMean r (negBinGammaProbability b) = (r : ℝ) / b := by
    unfold negBinCountMean negBinGammaProbability
    field_simp [ne_of_gt hb, ne_of_gt (show 0 < b + 1 by linarith)]
    <;> ring
  have hvariance :
      negBinCountVariance r (negBinGammaProbability b) =
        (r : ℝ) / b + (r : ℝ) / b ^ 2 := by
    unfold negBinCountVariance negBinGammaProbability
    field_simp [ne_of_gt hb, ne_of_gt (show 0 < b + 1 by linarith)]
    <;> ring
  have hden : 0 < b + 1 := by linarith
  have hp : 0 ≤ 1 / (b + 1) :=
    div_nonneg (by norm_num) (le_of_lt hden)
  have hcomp : 0 ≤ 1 - 1 / (b + 1) := by
    apply sub_nonneg.mpr
    rw [div_le_iff₀ hden]
    nlinarith
  refine ⟨?_, hmean, hvariance, ?_⟩
  · simpa [negBinGammaPredictive] using hrec
  · unfold negBinGammaPredictive negBinGammaProbability negBinCountMass
    positivity
