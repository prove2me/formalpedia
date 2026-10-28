-- Prove2me | solution 1 for AdaptiveCubic.FirstOrder.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:52:37.045926+00:00
-- url     : https://prove2.me/submissions/ad61e3b3-9ed9-4c61-9f94-a9464b4ca3bc

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : AdaptiveCubic.Cauchy.IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (h26 : ∀ k, AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) < f (x k))
    (flow : ℝ) (hflow : ∀ k, flow ≤ f (x k))
    (ε : ℝ) (hε : 0 < ε) (F : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k)
    (So : Set ℕ) (hSo : So ⊆ {k | η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧ ε < F k})
    (α p : ℝ) (hα : 0 < α) (hp : 0 < p)
    (h218 : ∀ k ∈ So, α * ε ^ p ≤ f (x k) - AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k)) :
    So.Finite ∧ (So.ncard : ℤ) ≤ ⌈(f (x 0) - flow) / (η₁ * α) * ε ^ (-p)⌉ := by
  classical
  have hη₁ : 0 < η₁ := hrun.2.2.1
  have hstep := hrun.2.2.2.2.2.2.2.2.1
  set c := η₁ * (α * ε ^ p) with hc
  have hεp : 0 < ε ^ p := Real.rpow_pos_of_pos hε p
  have hcpos : 0 < c := by positivity
  -- per-step decrease
  have hdec : ∀ k, 0 ≤ f (x k) - f (x (k + 1)) ∧ (k ∈ So → c ≤ f (x k) - f (x (k + 1))) := by
    intro k
    have hD : 0 < f (x k) - AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) := by
      linarith [h26 k]
    by_cases hr : η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k)
    · rw [hstep k, if_pos hr]
      unfold AdaptiveCubic.Cauchy.rho at hr
      rw [le_div_iff₀ hD] at hr
      refine ⟨by nlinarith, fun hk => ?_⟩
      have := h218 k hk
      rw [hc]
      nlinarith
    · rw [hstep k, if_neg hr]
      refine ⟨by simp, fun hk => absurd (hSo hk).1 hr⟩
  -- telescoping bound
  have htel : ∀ N, (((Finset.range N).filter (· ∈ So)).card : ℝ) * c ≤ f (x 0) - f (x N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hN : N ∈ So
      · rw [if_pos hN, Finset.card_insert_of_notMem (by simp)]
        push_cast
        have := (hdec N).2 hN
        linarith
      · rw [if_neg hN]
        have := (hdec N).1
        linarith
  have hbound : ∀ t : Finset ℕ, (↑t : Set ℕ) ⊆ So → (t.card : ℝ) * c ≤ f (x 0) - flow := by
    intro t ht
    set N := t.sup id + 1
    have hsub : t ⊆ (Finset.range N).filter (· ∈ So) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) hk), ht hk⟩
    have h1 := Finset.card_le_card hsub
    have h2 := htel N
    have h3 := hflow N
    have : (t.card : ℝ) ≤ (((Finset.range N).filter (· ∈ So)).card : ℝ) := by exact_mod_cast h1
    nlinarith
  set C := (f (x 0) - flow) / c with hC
  have hfin : So.Finite := by
    by_contra hinf
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈C⌉₊ + 1)
    have := hbound t ht
    rw [htc] at this
    have h2 : (⌈C⌉₊ + 1 : ℝ) ≤ C := by
      rw [hC, le_div_iff₀ hcpos]; exact_mod_cast this
    have h3 := Nat.le_ceil C
    linarith
  refine ⟨hfin, ?_⟩
  have hnc : (So.ncard : ℝ) ≤ C := by
    have := hbound hfin.toFinset (by simp)
    rw [← Set.ncard_eq_toFinset_card So hfin] at this
    rw [hC, le_div_iff₀ hcpos]; exact this
  have hCeq : C = (f (x 0) - flow) / (η₁ * α) * ε ^ (-p) := by
    rw [hC, hc, Real.rpow_neg hε.le]
    field_simp
  rw [← hCeq]
  have := hnc.trans (Int.le_ceil C)
  exact_mod_cast this
