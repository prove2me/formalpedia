-- Prove2me | solution 1 for AdWordsMSVV.Tradeoff.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:48:52.29703+00:00
-- url     : https://prove2.me/submissions/7c48e07d-3d77-4792-aa34-66c0adcdcfa5

import Mathlib
import Definitions.Def_AdWordsMSVV_Tradeoff_LP

set_option autoImplicit false
open AdWordsMSVV.Tradeoff Finset

lemma amt_dbl (α : ℕ → ℝ) (i : ℕ) :
    ∑ j ∈ Icc 1 i, ∑ l ∈ Icc 1 (j - 1), α l = ∑ l ∈ Icc 1 i, ((i : ℝ) - l) * α l := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
    simp only [add_tsub_cancel_right]
    have : ∑ l ∈ Icc 1 i, (((i + 1 : ℕ) : ℝ) - l) * α l
        = ∑ l ∈ Icc 1 i, ((i : ℝ) - l) * α l + ∑ l ∈ Icc 1 i, α l := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l _; push_cast; ring
    rw [this]
    push_cast
    ring

theorem solution (k N : ℕ) (hk : 1 ≤ k) (α β : ℕ → ℝ)
    (hβ : ∀ i ∈ Finset.Icc 1 k,
      β i = (N : ℝ) / k - (∑ j ∈ Finset.Icc 1 (i - 1), α j) / k) :
    ∀ i ∈ Finset.Icc 1 (k - 1),
      lVec k α i = bVec k N i + ∑ j ∈ Finset.Icc 1 i, (α j - β j) := by
  intro i hi
  rw [Finset.mem_Icc] at hi
  have h1 : ∑ j ∈ Icc 1 i, (α j - β j)
      = ∑ j ∈ Icc 1 i, α j - ∑ j ∈ Icc 1 i, ((N : ℝ) / k - (∑ l ∈ Icc 1 (j - 1), α l) / k) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [hβ j (Finset.mem_Icc.mpr ⟨hj.1, by omega⟩)]
  have h2 : ∑ j ∈ Icc 1 i, ((N : ℝ) / k - (∑ l ∈ Icc 1 (j - 1), α l) / k)
      = (i : ℝ) * ((N : ℝ) / k) - (∑ j ∈ Icc 1 i, ∑ l ∈ Icc 1 (j - 1), α l) / k := by
    rw [Finset.sum_sub_distrib, Finset.sum_div]
    simp [mul_div_assoc]
  have h3 : lVec k α i = ∑ j ∈ Icc 1 i, α j + (∑ l ∈ Icc 1 i, ((i : ℝ) - l) * α l) / k := by
    unfold lVec Aent
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [if_pos hj.2]; ring
  rw [h1, h2, h3, amt_dbl]
  unfold bVec
  ring
