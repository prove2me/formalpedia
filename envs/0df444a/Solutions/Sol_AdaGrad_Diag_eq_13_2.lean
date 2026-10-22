-- Prove2me | solution 2 for AdaGrad.Diag.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:17:50.690984+00:00
-- url     : https://prove2.me/submissions/60fe152c-c2b8-4689-bf8c-5c8785afe74f

import Mathlib
import Definitions.Def_AdaGrad_Diag_Setup
set_option autoImplicit false

theorem solution {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (δ : ℝ) (hδ : 0 ≤ δ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, AdaGrad.Diag.dualNormSq (AdaGrad.Diag.adaWeights δ g t) (g t) ≤
      2 * ∑ i, AdaGrad.Diag.s g T i := by
  have coord : ∀ (a : ℕ → ℝ) (T : ℕ),
      ∑ t ∈ Finset.Icc 1 T, a t ^ 2 / Real.sqrt (∑ τ ∈ Finset.Icc 1 t, a τ ^ 2)
        ≤ 2 * Real.sqrt (∑ τ ∈ Finset.Icc 1 T, a τ ^ 2) := by
    intro a T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      set A : ℝ := ∑ τ ∈ Finset.Icc 1 T, a τ ^ 2 with hA
      have hA0 : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      set B : ℝ := A + a (T + 1) ^ 2 with hB
      have hAB : A ≤ B := by simp [hB, sq_nonneg]
      have hB0 : 0 ≤ B := hA0.trans hAB
      have key : a (T + 1) ^ 2 / Real.sqrt B ≤ 2 * (Real.sqrt B - Real.sqrt A) := by
        rcases eq_or_lt_of_le hB0 with h0 | hpos
        · have hA' : A = 0 := le_antisymm (h0 ▸ hAB) hA0
          have : a (T + 1) ^ 2 = 0 := by rw [hB] at h0; linarith
          rw [← h0] at *
          simp [this, hA']
        · have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hpos
          rw [div_le_iff₀ hsB]
          have e1 : a (T + 1) ^ 2 = B - A := by rw [hB]; ring
          have e2 : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB0
          have e3 : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA0
          rw [e1]
          nlinarith [sq_nonneg (Real.sqrt B - Real.sqrt A)]
      linarith
  have hcmp : ∀ (t : ℕ) (i : Fin d), 1 ≤ t → g t i ^ 2 / (δ + AdaGrad.Diag.s g t i)
      ≤ g t i ^ 2 / AdaGrad.Diag.s g t i := by
    intro t i ht
    · have hs0 : 0 ≤ AdaGrad.Diag.s g t i := Real.sqrt_nonneg _
      rcases eq_or_lt_of_le hs0 with h0 | hpos
      · -- s = 0 forces g t i = 0
        have hsum : ∑ τ ∈ Finset.Icc 1 t, (g τ i) ^ 2 = 0 := by
          unfold AdaGrad.Diag.s at h0
          have := h0.symm
          rwa [Real.sqrt_eq_zero (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at this
        have hmem : t ∈ Finset.Icc 1 t := Finset.mem_Icc.mpr ⟨ht, le_refl t⟩
        have : g t i ^ 2 ≤ ∑ τ ∈ Finset.Icc 1 t, (g τ i) ^ 2 :=
          Finset.single_le_sum (f := fun τ => (g τ i) ^ 2) (fun _ _ => sq_nonneg _) hmem
        have hg : g t i ^ 2 = 0 := le_antisymm (hsum ▸ this) (sq_nonneg _)
        simp [hg]
      · exact div_le_div_of_nonneg_left (sq_nonneg _) hpos (by linarith)
  calc ∑ t ∈ Finset.Icc 1 T, AdaGrad.Diag.dualNormSq (AdaGrad.Diag.adaWeights δ g t) (g t)
      ≤ ∑ t ∈ Finset.Icc 1 T, AdaGrad.Diag.dualNormSq (AdaGrad.Diag.s g t) (g t) := by
        apply Finset.sum_le_sum
        intro t ht
        have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
        unfold AdaGrad.Diag.dualNormSq AdaGrad.Diag.adaWeights
        apply Finset.sum_le_sum
        intro i _
        exact hcmp t i ht1
    _ ≤ 2 * ∑ i, AdaGrad.Diag.s g T i := by
        unfold AdaGrad.Diag.dualNormSq
        rw [Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        exact coord (fun t => g t i) T
