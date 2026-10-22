-- Prove2me | solution 1 for AdaptiveCubic.FirstOrder.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:24:01.19492+00:00
-- url     : https://prove2.me/submissions/377d0a50-2a8d-4c0a-9860-b72317035009

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

set_option autoImplicit false
open scoped RealInnerProductSpace
open AdaptiveCubic.Cauchy

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (j : ℕ) (γ₃ : ℝ) (hγ₃ : 0 < γ₃) (hγ₃' : γ₃ ≤ 1)
    (h210 : ∀ k ≤ j, η₂ < rho f (B k) (σ k) (x k) (s k) → γ₃ * σ k ≤ σ (k + 1))
    (σbar : ℝ) (hσbar : 0 < σbar) (h212 : ∀ k ≤ j + 1, σ k ≤ σbar) :
    (((Finset.range (j + 1)).filter
        (fun k => rho f (B k) (σ k) (x k) (s k) < η₁)).card : ℤ) ≤
      ⌈-(Real.log γ₃ / Real.log γ₁) *
          (((Finset.range (j + 1)).filter
          (fun k => η₁ ≤ rho f (B k) (σ k) (x k) (s k))).card : ℝ) +
        1 / Real.log γ₁ * Real.log (σbar / σ 0)⌉ := by
  obtain ⟨hγ1, hγ12, hη1, hη12, hη2, hσ0, hsa, hcauchy, hx, hσ⟩ := hrun
  have hlogγ1 : 0 < Real.log γ₁ := Real.log_pos hγ1
  set pS : ℕ → Prop := fun k => η₁ ≤ rho f (B k) (σ k) (x k) (s k) with hpS
  set pU : ℕ → Prop := fun k => rho f (B k) (σ k) (x k) (s k) < η₁ with hpU
  have hcS : ∀ m, ((Finset.range m).filter pS).card = ∑ i ∈ Finset.range m, if pS i then 1 else 0 := by
    intro m; rw [Finset.card_filter]
  have hcU : ∀ m, ((Finset.range m).filter pU).card = ∑ i ∈ Finset.range m, if pU i then 1 else 0 := by
    intro m; rw [Finset.card_filter]
  have key : ∀ m ≤ j + 1, 0 < σ m ∧
      σ 0 * γ₃ ^ ((Finset.range m).filter pS).card * γ₁ ^ ((Finset.range m).filter pU).card ≤ σ m := by
    intro m
    induction m with
    | zero => intro _; simp [hσ0]
    | succ m ih =>
      intro hm
      obtain ⟨hpos, hle⟩ := ih (by omega)
      have hmj : m ≤ j := by omega
      rw [hcS (m + 1), hcU (m + 1), Finset.sum_range_succ, Finset.sum_range_succ]
      rw [hcS m, hcU m] at hle
      have hσm := hσ m
      by_cases h1 : rho f (B m) (σ m) (x m) (s m) < η₁
      · have h2 := hσm.2.2 h1
        have hnS : ¬ pS m := by simp only [hpS]; push_neg; exact h1
        have hU : pU m := h1
        rw [if_neg hnS, if_pos hU, add_zero, pow_succ]
        refine ⟨by nlinarith [h2.1], ?_⟩
        calc σ 0 * γ₃ ^ (∑ i ∈ Finset.range m, if pS i then 1 else 0) *
              (γ₁ ^ (∑ i ∈ Finset.range m, if pU i then 1 else 0) * γ₁)
            = γ₁ * (σ 0 * γ₃ ^ (∑ i ∈ Finset.range m, if pS i then 1 else 0) *
              γ₁ ^ (∑ i ∈ Finset.range m, if pU i then 1 else 0)) := by ring
          _ ≤ γ₁ * σ m := mul_le_mul_of_nonneg_left hle (by linarith)
          _ ≤ σ (m + 1) := h2.1
      · push_neg at h1
        have hS : pS m := h1
        have hnU : ¬ pU m := by simp only [hpU]; push_neg; exact h1
        rw [if_pos hS, if_neg hnU, add_zero, pow_succ]
        by_cases h3 : η₂ < rho f (B m) (σ m) (x m) (s m)
        · have h4 := hσm.1 h3
          have h5 := h210 m hmj h3
          refine ⟨h4.1, ?_⟩
          calc σ 0 * (γ₃ ^ (∑ i ∈ Finset.range m, if pS i then 1 else 0) * γ₃) *
                γ₁ ^ (∑ i ∈ Finset.range m, if pU i then 1 else 0)
              = γ₃ * (σ 0 * γ₃ ^ (∑ i ∈ Finset.range m, if pS i then 1 else 0) *
                γ₁ ^ (∑ i ∈ Finset.range m, if pU i then 1 else 0)) := by ring
            _ ≤ γ₃ * σ m := mul_le_mul_of_nonneg_left hle hγ₃.le
            _ ≤ σ (m + 1) := h5
        · push_neg at h3
          have h4 := hσm.2.1 ⟨h1, h3⟩
          have h6 : γ₃ * σ m ≤ σ m := by nlinarith
          refine ⟨by linarith [h4.1], ?_⟩
          calc σ 0 * (γ₃ ^ (∑ i ∈ Finset.range m, if pS i then 1 else 0) * γ₃) *
                γ₁ ^ (∑ i ∈ Finset.range m, if pU i then 1 else 0)
              = γ₃ * (σ 0 * γ₃ ^ (∑ i ∈ Finset.range m, if pS i then 1 else 0) *
                γ₁ ^ (∑ i ∈ Finset.range m, if pU i then 1 else 0)) := by ring
            _ ≤ γ₃ * σ m := mul_le_mul_of_nonneg_left hle hγ₃.le
            _ ≤ σ m := h6
            _ ≤ σ (m + 1) := h4.1
  obtain ⟨hpos, hfin⟩ := key (j + 1) le_rfl
  have hfin2 : σ 0 * γ₃ ^ ((Finset.range (j + 1)).filter pS).card *
      γ₁ ^ ((Finset.range (j + 1)).filter pU).card ≤ σbar := hfin.trans (h212 _ le_rfl)
  set nS := ((Finset.range (j + 1)).filter pS).card with hnS
  set nU := ((Finset.range (j + 1)).filter pU).card with hnU
  have hlog := Real.log_le_log (by positivity) hfin2
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at hlog
  have hl2 : Real.log (σbar / σ 0) = Real.log σbar - Real.log (σ 0) :=
    Real.log_div hσbar.ne' hσ0.ne'
  have hreal : (nU : ℝ) ≤ -(Real.log γ₃ / Real.log γ₁) * nS +
      1 / Real.log γ₁ * Real.log (σbar / σ 0) := by
    rw [hl2]
    have : (nU : ℝ) * Real.log γ₁ ≤ Real.log σbar - Real.log (σ 0) - nS * Real.log γ₃ := by linarith
    have h3 : (nU : ℝ) ≤ (Real.log σbar - Real.log (σ 0) - nS * Real.log γ₃) / Real.log γ₁ :=
      (le_div_iff₀ hlogγ1).mpr this
    calc (nU : ℝ) ≤ _ := h3
      _ = _ := by field_simp; ring
  have := hreal.trans (Int.le_ceil _)
  exact_mod_cast this
