-- Prove2me | solution 1 for ActuarialValuation.utPremium_zero_loss
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:41:58.571596+00:00
-- url     : https://prove2.me/submissions/96f07a90-0099-4ff3-a765-e4eda14de9a0

import Mathlib
import Definitions.Def_actuarial_utExpectedStoploss
import Definitions.Def_actuarial_utPositiveStoploss
import Definitions.Def_actuarial_utDiscreteCDF
import Definitions.Def_actuarial_utRiskLoading
import Definitions.Def_actuarial_utInsuredUtility
import Definitions.Def_actuarial_utExpectedUninsured
import Definitions.Def_actuarial_utPremium
import Definitions.Def_actuarial_utLossMoment
import Definitions.Def_actuarial_utExpectedUtility
import Definitions.Def_actuarial_utExpected
import Definitions.Def_actuarial_utArrowPratt
import Definitions.Def_actuarial_utCARASecond
import Definitions.Def_actuarial_utCARADerivative
import Definitions.Def_actuarial_utCARA
set_option autoImplicit false
noncomputable section
open ActuarialValuation

private lemma positive_moment {n : ℕ} (p loss : Fin n → ℝ) (a : ℝ)
    (hp : ∀ k, 0 ≤ p k) (hn : (∑ k, p k) = 1) : 0 < utLossMoment p loss a := by
  have hex : ∃ k, 0 < p k := by
    by_contra h
    push_neg at h
    have hz : ∀ k, p k = 0 := fun k => le_antisymm (h k) (hp k)
    simp [hz] at hn
  obtain ⟨k, hk⟩ := hex
  unfold utLossMoment utExpected
  exact Finset.sum_pos' (fun j hj => mul_nonneg (hp j) (Real.exp_pos _).le)
    ⟨k, Finset.mem_univ k, mul_pos hk (Real.exp_pos _)⟩

private lemma premium_constant {n : ℕ} (p : Fin n → ℝ) (loss a : ℝ)
    (ha : a ≠ 0) (hn : (∑ k, p k) = 1) : utPremium p (fun _ => loss) a = loss := by
  unfold utPremium utLossMoment utExpected
  rw [← Finset.sum_mul, hn, one_mul, Real.log_exp]
  exact mul_div_cancel_left₀ loss ha

private lemma reconstruct {n : ℕ} (p loss : Fin n → ℝ) (a : ℝ)
    (ha : a ≠ 0) (hp : ∀ k, 0 ≤ p k) (hn : (∑ k, p k) = 1) :
    Real.exp (a * utPremium p loss a) = utLossMoment p loss a := by
  have he : a * utPremium p loss a = Real.log (utLossMoment p loss a) := by
    unfold utPremium
    field_simp
  rw [he, Real.exp_log (positive_moment p loss a hp hn)]

private lemma uninsured_factor {n : ℕ} (p loss : Fin n → ℝ) (a wealth : ℝ) :
    utExpectedUninsured p loss a wealth = -Real.exp (-a*wealth) * utLossMoment p loss a := by
  unfold utExpectedUninsured utExpectedUtility utCARA utLossMoment utExpected
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only
  rw [show -a * (wealth-loss k) = -a*wealth+a*loss k by ring, Real.exp_add]
  ring

private lemma indifference {n : ℕ} (p loss : Fin n → ℝ) (a wealth : ℝ)
    (ha : a ≠ 0) (hp : ∀ k, 0 ≤ p k) (hn : (∑ k, p k) = 1) :
    utInsuredUtility a wealth (utPremium p loss a) = utExpectedUninsured p loss a wealth := by
  rw [uninsured_factor]
  unfold utInsuredUtility utCARA
  rw [show -a*(wealth-utPremium p loss a) = -a*wealth+a*utPremium p loss a by ring,
    Real.exp_add, reconstruct p loss a ha hp hn]
  ring

private lemma loading_nonneg {n : ℕ} (p loss : Fin n → ℝ) (a : ℝ)
    (ha : 0 < a) (hp : ∀ k, 0 ≤ p k) (hn : (∑ k, p k) = 1) : 0 ≤ utRiskLoading p loss a := by
  have hJ := ConvexOn.map_sum_le convexOn_exp (t := Finset.univ) (w := p)
    (p := fun k => a*loss k) (fun k hk => hp k) hn (fun k hk => Set.mem_univ _)
  have he : Real.exp (a * utExpected p loss) ≤ utLossMoment p loss a := by
    simpa [utExpected, utLossMoment, smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm] using hJ
  have hl := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hl
  unfold utRiskLoading utPremium
  apply sub_nonneg.mpr
  apply (le_div_iff₀ ha).mpr
  nlinarith

private lemma stoploss_order {n : ℕ} (p x y : Fin n → ℝ) (r : ℝ)
    (hp : ∀ k, 0 ≤ p k) (hxy : ∀ k, x k ≤ y k) :
    utExpectedStoploss p x r ≤ utExpectedStoploss p y r := by
  unfold utExpectedStoploss utExpected utPositiveStoploss
  exact Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left
    (max_le_max_left 0 (sub_le_sub_right (hxy k) r)) (hp k))
theorem solution {n : ℕ} (p : Fin n → ℝ) (a : ℝ) (ha : a≠0) (hp : (∑ k : Fin n, p k)=1) : utPremium p (fun _ => 0) a=0 := by
  classical

  exact premium_constant p 0 a ha hp

#print axioms solution
