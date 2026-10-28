-- Prove2me | solution 1 for AdaptiveCubic.FirstOrder.theorem_2_1_sigma_min
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:50:16.121599+00:00
-- url     : https://prove2.me/submissions/302946f2-10d9-46a4-aedd-a692e34ed560

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : AdaptiveCubic.Cauchy.IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (σmin : ℝ) (hσmin : 0 < σmin) (h211 : ∀ k, σmin ≤ σ k)
    (j : ℕ) (σbar : ℝ) (hσbar : 0 < σbar) (h212 : ∀ k ≤ j + 1, σ k ≤ σbar) :
    (((Finset.range (j + 1)).filter
        (fun k => AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) < η₁)).card : ℤ) ≤
      ⌈((((Finset.range (j + 1)).filter
            (fun k => η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))).card : ℝ) + 1) *
        (1 / Real.log γ₁) * Real.log (σbar / σmin)⌉ := by
  set ρ := fun k => AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) with hρ
  have hγ : 1 < γ₁ := hrun.1
  have hlγ : 0 < Real.log γ₁ := Real.log_pos hγ
  have hupd := hrun.2.2.2.2.2.2.2.2.2
  set K := Real.log (σbar / σmin) with hK
  let U : ℕ → ℕ := fun m => ((Finset.range m).filter (fun k => ρ k < η₁)).card
  let S : ℕ → ℕ := fun m => ((Finset.range m).filter (fun k => η₁ ≤ ρ k)).card
  have hσpos : ∀ k, 0 < σ k := fun k => lt_of_lt_of_le hσmin (h211 k)
  have hlog0 : ∀ k, 0 ≤ Real.log (σ k / σmin) := fun k =>
    Real.log_nonneg ((one_le_div hσmin).mpr (h211 k))
  have hlogK : ∀ k ≤ j + 1, Real.log (σ k / σmin) ≤ K := by
    intro k hk
    exact Real.log_le_log (div_pos (hσpos k) hσmin)
      (div_le_div_of_nonneg_right (h212 k hk) hσmin.le)
  have hUsucc : ∀ m, U (m + 1) = U m + (if ρ m < η₁ then 1 else 0) := by
    intro m
    simp only [U, Finset.card_filter, Finset.sum_range_succ]
  have hSsucc : ∀ m, S (m + 1) = S m + (if η₁ ≤ ρ m then 1 else 0) := by
    intro m
    simp only [S, Finset.card_filter, Finset.sum_range_succ]
  have key : ∀ m, m ≤ j + 1 → (U m : ℝ) * Real.log γ₁ ≤ (S m : ℝ) * K + Real.log (σ m / σmin) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [U, S, Finset.range_zero, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
        zero_mul, zero_add]
      exact hlog0 0
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      rw [hUsucc, hSsucc]
      by_cases hr : ρ m < η₁
      · have hnr : ¬ η₁ ≤ ρ m := not_le.mpr hr
        rw [if_pos hr, if_neg hnr]
        push_cast
        have hgrow : γ₁ * σ m ≤ σ (m + 1) := ((hupd m).2.2 hr).1
        have hl : Real.log γ₁ + Real.log (σ m / σmin) ≤ Real.log (σ (m + 1) / σmin) := by
          have hg0 : γ₁ ≠ 0 := by linarith
          rw [← Real.log_mul hg0 (div_pos (hσpos m) hσmin).ne']
          apply Real.log_le_log (mul_pos (by linarith) (div_pos (hσpos m) hσmin))
          rw [← mul_div_assoc]
          exact div_le_div_of_nonneg_right hgrow hσmin.le
        nlinarith
      · rw [if_neg hr, if_pos (not_lt.mp hr)]
        push_cast
        have h1 := hlogK m (by omega)
        have h2 := hlog0 (m + 1)
        nlinarith
  have hfin := key (j + 1) le_rfl
  have hK' := hlogK (j + 1) le_rfl
  have hU : (U (j + 1) : ℝ) ≤ ((S (j + 1) : ℝ) + 1) * (1 / Real.log γ₁) * K := by
    rw [mul_one_div, ← mul_div_right_comm, le_div_iff₀ hlγ]
    nlinarith
  have := hU.trans (Int.le_ceil _)
  exact_mod_cast this
