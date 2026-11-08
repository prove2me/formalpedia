-- Prove2me | solution 1 for AllPhotonicRepeater.indirectZSuccess_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:32:09.281625+00:00
-- url     : https://prove2.me/submissions/7b5f27a1-eaef-4713-af40-e1e94797bdf1

import Mathlib
import Definitions.Def_AllPhotonicRepeater_zSuccess
import Definitions.Def_AllPhotonicRepeater_xSuccess

set_option autoImplicit false

open AllPhotonicRepeater in
theorem solution (ε0 : ℝ) (h0 : 0 ≤ ε0) (h1 : ε0 ≤ 1) (l : ℕ) (b : ℕ → ℕ) :
    (∀ k : ℕ, 0 ≤ indirectZSuccess ε0 l b k ∧ indirectZSuccess ε0 l b k ≤ 1) ∧
    (0 ≤ zSuccess ε0 l b ∧ zSuccess ε0 l b ≤ 1) ∧
    (0 ≤ xSuccess ε0 l b ∧ xSuccess ε0 l b ≤ 1) := by
  have unit : ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ n : ℕ, 0 ≤ a ^ n ∧ a ^ n ≤ 1 :=
    fun a ha0 ha1 n => ⟨pow_nonneg ha0 n, pow_le_one₀ ha0 ha1⟩
  have hu : ∀ I : ℝ, 0 ≤ I → I ≤ 1 → 0 ≤ 1 - ε0 + ε0 * I ∧ 1 - ε0 + ε0 * I ≤ 1 := by
    intro I hI0 hI1
    constructor
    · nlinarith [mul_nonneg h0 hI0]
    · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hI1)]
  have key : ∀ n k : ℕ, l + 1 - k ≤ n →
      0 ≤ indirectZSuccess ε0 l b k ∧ indirectZSuccess ε0 l b k ≤ 1 := by
    intro n
    induction n with
    | zero =>
      intro k hk
      rw [indirectZSuccess, dif_neg (by omega)]
      exact ⟨le_refl 0, zero_le_one⟩
    | succ n ih =>
      intro k hk
      rw [indirectZSuccess]
      by_cases hkl : k ≤ l
      · rw [dif_pos hkl]
        obtain ⟨hI0, hI1⟩ := ih (k + 2) (by omega)
        generalize (if k + 1 ≤ l then b (k + 1) else 0) = e
        obtain ⟨hu0, hu1⟩ := hu _ hI0 hI1
        obtain ⟨hp0, hp1⟩ := unit _ hu0 hu1 e
        have hv0 : 0 ≤ 1 - (1 - ε0) * (1 - ε0 + ε0 * indirectZSuccess ε0 l b (k + 2)) ^ e := by
          have := mul_le_one₀ (by linarith : 1 - ε0 ≤ 1) hp0 hp1
          linarith
        have hv1 : 1 - (1 - ε0) * (1 - ε0 + ε0 * indirectZSuccess ε0 l b (k + 2)) ^ e ≤ 1 := by
          have := mul_nonneg (sub_nonneg.mpr h1) hp0
          linarith
        obtain ⟨hq0, hq1⟩ := unit _ hv0 hv1 (b k)
        constructor <;> linarith
      · rw [dif_neg hkl]
        exact ⟨le_refl 0, zero_le_one⟩
  have hall : ∀ k, 0 ≤ indirectZSuccess ε0 l b k ∧ indirectZSuccess ε0 l b k ≤ 1 :=
    fun k => key (l + 1 - k) k le_rfl
  refine ⟨hall, ?_, ?_⟩
  · unfold zSuccess
    obtain ⟨hu0, hu1⟩ := hu _ (hall 1).1 (hall 1).2
    exact unit _ hu0 hu1 _
  · exact hall 0
