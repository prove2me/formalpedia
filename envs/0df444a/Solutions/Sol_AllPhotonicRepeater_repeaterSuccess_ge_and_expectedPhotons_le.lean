-- Prove2me | solution 1 for AllPhotonicRepeater.repeaterSuccess_ge_and_expectedPhotons_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T07:29:07.021113+00:00
-- url     : https://prove2.me/submissions/d7e897c6-913e-4fb4-a5c1-734509016299

import Mathlib
import Definitions.Def_AllPhotonicRepeater_expectedPhotons

set_option autoImplicit false

open AllPhotonicRepeater in
theorem solution (ε0 : ℝ) (h0 : 0 ≤ ε0) (h1 : ε0 ≤ 1)
    (n m l : ℕ) (b : ℕ → ℕ) (δ : ℝ) (hm : 1 ≤ m)
    (hZ : 1 - zSuccess ε0 l b ≤ δ) (hX : 1 - xSuccess ε0 l b ≤ δ)
    (hδ : 2 * (m : ℝ) * n * δ ≤ 1 / 2)
    (hB : 1 / 4 ≤ (1 - (1 - bellSuccess ε0) ^ m) ^ (n + 1)) :
    1 / 8 ≤ repeaterSuccess ε0 n m l b ∧
      expectedPhotons ε0 n m l b ≤
        8 * (2 * (m : ℝ) * n * ((treeSize l b : ℝ) + 1) + 2 * m) := by
  have hZX : 1 / 2 ≤ zSuccess ε0 l b ^ (2 * (m - 1) * n) * xSuccess ε0 l b ^ (2 * n) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; norm_num
    · have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hmn : (1 : ℝ) ≤ m * n := by nlinarith
      have hδ4 : δ ≤ 1 / 4 := by
        rcases le_or_gt δ 0 with h | h
        · linarith
        · nlinarith
      have h0δ : 0 ≤ 1 - δ := by linarith
      have hZ' : 1 - δ ≤ zSuccess ε0 l b := by linarith
      have hX' : 1 - δ ≤ xSuccess ε0 l b := by linarith
      have hprod : (1 - δ) ^ (2 * (m - 1) * n) * (1 - δ) ^ (2 * n) ≤
          zSuccess ε0 l b ^ (2 * (m - 1) * n) * xSuccess ε0 l b ^ (2 * n) :=
        mul_le_mul (pow_le_pow_left₀ h0δ hZ' _) (pow_le_pow_left₀ h0δ hX' _)
          (pow_nonneg h0δ _) (pow_nonneg (h0δ.trans hZ') _)
      have hexp : 2 * (m - 1) * n + 2 * n = 2 * m * n := by
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      rw [← pow_add, hexp] at hprod
      have hber := one_add_mul_le_pow (a := -δ) (by linarith) (2 * m * n)
      push_cast at hber
      rw [← sub_eq_add_neg] at hber
      nlinarith
  have hP : 1 / 8 ≤ repeaterSuccess ε0 n m l b := by
    unfold repeaterSuccess
    have := mul_le_mul hZX hB (by norm_num) (by linarith)
    linarith
  refine ⟨hP, ?_⟩
  unfold expectedPhotons
  have hPpos : 0 < repeaterSuccess ε0 n m l b := by linarith
  rw [div_le_iff₀ hPpos]
  have hN : 0 ≤ 2 * (m : ℝ) * n * ((treeSize l b : ℝ) + 1) + 2 * m := by positivity
  nlinarith
