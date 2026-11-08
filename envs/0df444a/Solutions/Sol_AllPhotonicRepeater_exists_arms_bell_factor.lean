-- Prove2me | solution 1 for AllPhotonicRepeater.exists_arms_bell_factor
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:58:36.136197+00:00
-- url     : https://prove2.me/submissions/e65d2d31-0a0d-4667-893d-3a4aea0bdcdb

import Mathlib
import Definitions.Def_AllPhotonicRepeater_bellSuccess

set_option autoImplicit false

open AllPhotonicRepeater in
theorem solution (ε0 : ℝ) (h0 : 0 ≤ ε0) (h1 : ε0 < 1) :
    ∃ C : ℝ, ∀ n : ℕ, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((n : ℝ) + 1) ∧
      1 / 4 ≤ (1 - (1 - bellSuccess ε0) ^ m) ^ (n + 1) := by
  have hb0 : 0 < bellSuccess ε0 := by
    unfold bellSuccess
    have : 0 < 1 - ε0 := by linarith
    positivity
  have hb1 : bellSuccess ε0 ≤ 1 / 2 := by
    unfold bellSuccess
    have : (1 - ε0) ^ 2 ≤ 1 := by nlinarith
    linarith
  obtain ⟨q, hq⟩ : ∃ q, q = 1 - bellSuccess ε0 := ⟨_, rfl⟩
  rw [← hq]
  have hq0 : 0 ≤ q := by linarith
  have hq1 : q < 1 := by linarith
  obtain ⟨c, hc⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hq1
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; norm_num at hc
    · exact h
  have h2 : ∀ k : ℕ, (k : ℝ) + 1 ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      push_cast
      rw [pow_succ]
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      linarith
  refine ⟨c, fun n => ⟨c * (n + 1), Nat.succ_le_of_lt (Nat.mul_pos hc1 (Nat.succ_pos n)),
    by push_cast; exact le_rfl, ?_⟩⟩
  obtain ⟨x, hx⟩ : ∃ x, x = q ^ (c * (n + 1)) := ⟨_, rfl⟩
  rw [← hx]
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hxle : x ≤ (1 / 2) ^ (n + 1) := by
    rw [hx, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hq0 c) hc.le _
  have hhalf : ((n : ℝ) + 1) * (1 / 2) ^ (n + 1) ≤ 1 / 2 := by
    have e : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
    have hp : 0 ≤ ((1 : ℝ) / 2) ^ n := by positivity
    rw [pow_succ]
    nlinarith [h2 n]
  have hnx : ((n : ℝ) + 1) * x ≤ 1 / 2 :=
    le_trans (mul_le_mul_of_nonneg_left hxle (by positivity)) hhalf
  have hx1 : x ≤ 1 := by
    have : ((1 : ℝ) / 2) ^ (n + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hber := one_add_mul_le_pow (a := -x) (by linarith) (n + 1)
  have e : (1 + -x) = 1 - x := by ring
  rw [e] at hber
  push_cast at hber
  linarith
