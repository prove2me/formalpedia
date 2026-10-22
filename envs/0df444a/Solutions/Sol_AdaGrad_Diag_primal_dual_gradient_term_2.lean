-- Prove2me | solution 2 for AdaGrad.Diag.primal_dual_gradient_term
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:27:32.845981+00:00
-- url     : https://prove2.me/submissions/d3d85e96-d822-485d-b85a-74be71b7bfd5

import Mathlib
import Definitions.Def_AdaGrad_Diag_Setup
set_option autoImplicit false

theorem solution {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (δ : ℝ)
    (hδ : 0 ≤ δ) (T : ℕ) (hδg : ∀ t ∈ Finset.Icc 1 T, AdaGrad.Diag.supNorm (g t) ≤ δ) :
    ∑ t ∈ Finset.Icc 1 T, AdaGrad.Diag.dualNormSq (AdaGrad.Diag.adaWeights δ g (t - 1)) (g t)
      ≤ 2 * ∑ i, AdaGrad.Diag.s g T i := by
  have coord : ∀ (a : ℕ → ℝ) (T : ℕ), (∀ t ∈ Finset.Icc 1 T, |a t| ≤ δ) →
      ∑ t ∈ Finset.Icc 1 T, a t ^ 2 / (δ + Real.sqrt (∑ τ ∈ Finset.Icc 1 (t - 1), a τ ^ 2))
        ≤ 2 * Real.sqrt (∑ τ ∈ Finset.Icc 1 T, a τ ^ 2) := by
    intro a T
    induction T with
    | zero => intro _; simp
    | succ T ih =>
      intro hb
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      have ih' := ih (fun t ht => hb t (by
        simp only [Finset.mem_Icc] at ht ⊢; omega))
      have haT : |a (T + 1)| ≤ δ := hb (T + 1) (by simp)
      simp only [Nat.add_sub_cancel]
      set A : ℝ := ∑ τ ∈ Finset.Icc 1 T, a τ ^ 2 with hA
      have hA0 : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      set B : ℝ := A + a (T + 1) ^ 2 with hB
      have hAB : A ≤ B := by simp [hB, sq_nonneg]
      have hB0 : 0 ≤ B := hA0.trans hAB
      have hsA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
      have e2 : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB0
      have e3 : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA0
      have hsAB : Real.sqrt A ≤ Real.sqrt B := Real.sqrt_le_sqrt hAB
      have hsq : a (T + 1) ^ 2 ≤ δ ^ 2 := by
        have := sq_le_sq' (by linarith [abs_le.mp haT]) (abs_le.mp haT).2
        exact this
      have hBle : Real.sqrt B ≤ Real.sqrt A + δ := by
        apply Real.sqrt_le_iff.mpr
        refine ⟨by linarith, ?_⟩
        nlinarith
      have key : a (T + 1) ^ 2 / (δ + Real.sqrt A) ≤ 2 * (Real.sqrt B - Real.sqrt A) := by
        rcases eq_or_lt_of_le (add_nonneg hδ hsA) with h0 | hpos
        · have hd0 : δ = 0 := by linarith
          have : a (T + 1) ^ 2 = 0 := by nlinarith
          rw [← h0]; simp [this]
          nlinarith
        · rw [div_le_iff₀ hpos]
          have e1 : a (T + 1) ^ 2 = B - A := by rw [hB]; ring
          rw [e1]
          have : B - A = (Real.sqrt B - Real.sqrt A) * (Real.sqrt B + Real.sqrt A) := by nlinarith
          rw [this]
          have h5 : Real.sqrt B + Real.sqrt A ≤ 2 * (δ + Real.sqrt A) := by linarith
          have h6 : 0 ≤ Real.sqrt B - Real.sqrt A := by linarith
          nlinarith
      linarith
  have hcoord : ∀ i : Fin d, ∀ t ∈ Finset.Icc 1 T, |g t i| ≤ δ := by
    intro i t ht
    refine le_trans ?_ (hδg t ht)
    unfold AdaGrad.Diag.supNorm
    exact le_ciSup (f := fun j : Fin d => |g t j|) (Set.finite_range _).bddAbove i
  unfold AdaGrad.Diag.dualNormSq AdaGrad.Diag.adaWeights AdaGrad.Diag.s
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact coord (fun t => g t i) T (hcoord i)
