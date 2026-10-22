-- Prove2me | solution 1 for AdaptiveCubic.Cauchy.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:13:06.323535+00:00
-- url     : https://prove2.me/submissions/5ee7bd77-3769-49f5-a08a-30c260f6e45f

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

set_option autoImplicit false
open scoped RealInnerProductSpace
open AdaptiveCubic.Cauchy

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (flow : ℝ) (hlow : ∀ k, flow ≤ f (x k))
    (ε : ℝ) (hε : 0 < ε) (α p : ℝ) (hα : 0 < α) (hp : 0 < p) (j : ℕ)
    (h26 : ∀ k ≤ j, model f (B k) (σ k) (x k) (s k) < f (x k))
    (So : Finset ℕ)
    (hSo : So ⊆ (Finset.range (j + 1)).filter (fun k => η₁ ≤ rho f (B k) (σ k) (x k) (s k)))
    (h218 : ∀ k ∈ So, α * ε ^ p ≤ f (x k) - model f (B k) (σ k) (x k) (s k)) :
    (So.card : ℤ) ≤ ⌈(f (x 0) - flow) / (η₁ * α) * ε ^ (-p)⌉ := by
  obtain ⟨hγ1, hγ12, hη1, hη12, hη2, hσ0, hsa, hcauchy, hx, hσ⟩ := hrun
  have hsucc : ∀ k ≤ j, η₁ ≤ rho f (B k) (σ k) (x k) (s k) →
      η₁ * (f (x k) - model f (B k) (σ k) (x k) (s k)) ≤ f (x k) - f (x (k + 1)) := by
    intro k hk h
    rw [hx k, if_pos h]
    have hpos : 0 < f (x k) - model f (B k) (σ k) (x k) (s k) := by linarith [h26 k hk]
    unfold rho at h
    rw [le_div_iff₀ hpos] at h
    linarith
  have hdec : ∀ k ≤ j, 0 ≤ f (x k) - f (x (k + 1)) := by
    intro k hk
    by_cases h : η₁ ≤ rho f (B k) (σ k) (x k) (s k)
    · have := hsucc k hk h
      have hpos : 0 < f (x k) - model f (B k) (σ k) (x k) (s k) := by linarith [h26 k hk]
      nlinarith
    · rw [hx k, if_neg h]; simp
  have hsum : ∑ k ∈ Finset.range (j + 1), (f (x k) - f (x (k + 1))) = f (x 0) - f (x (j + 1)) :=
    Finset.sum_range_sub' (fun k => f (x k)) (j + 1)
  have hSsub : ∑ k ∈ So, (f (x k) - f (x (k + 1))) ≤
      ∑ k ∈ Finset.range (j + 1), (f (x k) - f (x (k + 1))) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk; exact (Finset.mem_filter.mp (hSo hk)).1
    · intro k hk _; exact hdec k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hlow2 : (So.card : ℝ) * (η₁ * (α * ε ^ p)) ≤ ∑ k ∈ So, (f (x k) - f (x (k + 1))) := by
    have : ∑ k ∈ So, (η₁ * (α * ε ^ p)) ≤ ∑ k ∈ So, (f (x k) - f (x (k + 1))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_filter.mp (hSo hk)
      have h1 := hsucc k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk'.1)) hk'.2
      have h2 := h218 k hk
      nlinarith
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hD : (So.card : ℝ) * (η₁ * (α * ε ^ p)) ≤ f (x 0) - flow := by
    have := hlow (j + 1)
    linarith
  have hpos : 0 < η₁ * (α * ε ^ p) := by positivity
  have hreal : (So.card : ℝ) ≤ (f (x 0) - flow) / (η₁ * α) * ε ^ (-p) := by
    rw [Real.rpow_neg hε.le, ← div_eq_mul_inv, div_div]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hD]
  have := hreal.trans (Int.le_ceil _)
  exact_mod_cast this
