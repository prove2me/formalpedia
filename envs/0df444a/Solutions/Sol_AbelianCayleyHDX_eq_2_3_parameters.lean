-- Prove2me | solution 1 for AbelianCayleyHDX.eq_2_3_parameters
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:35:34.438067+00:00
-- url     : https://prove2.me/submissions/cac047cb-1649-414b-a621-9b8730d68db2

import Mathlib
namespace AbelianCayleyHDX

theorem eq_2_3_parameters :
    (∀ h t n : ℕ, 1 ≤ h → 2 * (h : ℝ) * (2 : ℝ) ^ ((t : ℝ) / 3) ≤ n →
      (((2 : ℝ) ^ h) ^ 2 - 1) * ((2 : ℝ) ^ h) ^ (2 * t) ≤
        (((2 : ℝ) ^ h) ^ 2 - 1) * ((n : ℝ) / (2 * h)) ^ (6 * h)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∃ h : ℕ, 8 ≤ 2 ^ h ∧ 3 / ((2 : ℝ) ^ h - 2) ≤ lam ∧
      (∀ h' < h, ¬ (8 ≤ 2 ^ h' ∧ 3 / ((2 : ℝ) ^ h' - 2) ≤ lam)) ∧
      (h : ℝ) ≤ C * Real.log (2 + 1 / lam)) ∧
    (∀ h t n : ℕ, 1 ≤ h → 2 * (h : ℝ) * (2 : ℝ) ^ ((t : ℝ) / 3) ≤ n →
      (t : ℝ) ≤ 3 * Real.logb 2 n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h t n hh hn
    have h0 : (0 : ℝ) < 2 * h := by have : (1 : ℝ) ≤ h := by exact_mod_cast hh
                                    linarith
    set s := (2 : ℝ) ^ ((t : ℝ) / 3) with hs
    have s0 : 0 ≤ s := by positivity
    have hsn : s ≤ (n : ℝ) / (2 * h) := by
      rw [le_div_iff₀ h0]; linarith
    have key : ((2 : ℝ) ^ h) ^ (2 * t) = s ^ (6 * h) := by
      rw [hs, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1; push_cast; ring
    have hq : 0 ≤ ((2 : ℝ) ^ h) ^ 2 - 1 := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ h := one_le_pow₀ (by norm_num)
      nlinarith
    rw [key]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ s0 hsn _) hq
  · refine ⟨4 / Real.log 2, by positivity, ?_⟩
    intro lam hlam
    classical
    set y : ℝ := 8 + 3 / lam with hy
    have y0 : 0 < y := by positivity
    set W : ℕ := ⌈Real.logb 2 y⌉₊ with hW
    have hW1 : y ≤ (2 : ℝ) ^ W := by
      have : Real.logb 2 y ≤ (W : ℝ) := Nat.le_ceil _
      calc y = (2 : ℝ) ^ (Real.logb 2 y) := (Real.rpow_logb (by norm_num) (by norm_num) y0).symm
        _ ≤ (2 : ℝ) ^ (W : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) this
        _ = (2 : ℝ) ^ W := Real.rpow_natCast _ _
    have P : ∀ k : ℕ, y ≤ (2 : ℝ) ^ k → 8 ≤ 2 ^ k ∧ 3 / ((2 : ℝ) ^ k - 2) ≤ lam := by
      intro k hk
      have h3 : 0 < 3 / lam := by positivity
      refine ⟨?_, ?_⟩
      · have : (8 : ℝ) ≤ (2 : ℝ) ^ k := by linarith
        exact_mod_cast this
      · rw [div_le_iff₀ (by linarith)]
        have : lam * (3 / lam) = 3 := by field_simp
        nlinarith
    have hex : ∃ k : ℕ, 8 ≤ 2 ^ k ∧ 3 / ((2 : ℝ) ^ k - 2) ≤ lam := ⟨W, P W hW1⟩
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun h' hh' => Nat.find_min hex hh', ?_⟩
    have hle : Nat.find hex ≤ W := Nat.find_min' hex (P W hW1)
    have hWlt : (W : ℝ) < Real.logb 2 y + 1 := Nat.ceil_lt_add_one (by
      apply Real.logb_nonneg (by norm_num); linarith [show 0 < 3 / lam by positivity])
    set x := Real.log (2 + 1 / lam) with hx
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hx2 : Real.log 2 ≤ x := Real.log_le_log (by norm_num) (by linarith [show 0 < 1 / lam by positivity])
    have hy4 : y ≤ 4 * (2 + 1 / lam) := by rw [hy]; have : 0 < 1 / lam := by positivity
                                           have e : 3 / lam = 3 * (1 / lam) := by ring
                                           rw [e]; linarith
    have hlogy : Real.log y ≤ Real.log 4 + x := by
      rw [hx, ← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log y0 hy4
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hlogb : Real.logb 2 y ≤ 2 + x / Real.log 2 := by
      rw [Real.logb, div_le_iff₀ hl2]
      rw [add_mul, div_mul_cancel₀ _ hl2.ne']
      linarith
    have : (Nat.find hex : ℝ) ≤ W := by exact_mod_cast hle
    have hfin : 3 + x / Real.log 2 ≤ 4 / Real.log 2 * x := by
      have : 1 ≤ x / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
      have e : 4 / Real.log 2 * x = 4 * (x / Real.log 2) := by ring
      rw [e]; linarith
    linarith
  · intro h t n hh hn
    have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
    set s := (2 : ℝ) ^ ((t : ℝ) / 3) with hs
    have s0 : 0 < s := by positivity
    have hsn : s ≤ n := by nlinarith
    have : (t : ℝ) / 3 ≤ Real.logb 2 n := by
      have e : Real.logb 2 s = (t : ℝ) / 3 := by
        rw [hs, Real.logb_rpow (by norm_num) (by norm_num)]
      rw [← e]
      exact Real.logb_le_logb_of_le (by norm_num) s0 hsn
    linarith

end AbelianCayleyHDX

theorem solution :
    (∀ h t n : ℕ, 1 ≤ h → 2 * (h : ℝ) * (2 : ℝ) ^ ((t : ℝ) / 3) ≤ n →
      (((2 : ℝ) ^ h) ^ 2 - 1) * ((2 : ℝ) ^ h) ^ (2 * t) ≤
        (((2 : ℝ) ^ h) ^ 2 - 1) * ((n : ℝ) / (2 * h)) ^ (6 * h)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∃ h : ℕ, 8 ≤ 2 ^ h ∧ 3 / ((2 : ℝ) ^ h - 2) ≤ lam ∧
      (∀ h' < h, ¬ (8 ≤ 2 ^ h' ∧ 3 / ((2 : ℝ) ^ h' - 2) ≤ lam)) ∧
      (h : ℝ) ≤ C * Real.log (2 + 1 / lam)) ∧
    (∀ h t n : ℕ, 1 ≤ h → 2 * (h : ℝ) * (2 : ℝ) ^ ((t : ℝ) / 3) ≤ n →
      (t : ℝ) ≤ 3 * Real.logb 2 n) :=
  AbelianCayleyHDX.eq_2_3_parameters
