-- Prove2me | solution 1 for AdaptiveCubic.SecondOrder.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:47:22.232042+00:00
-- url     : https://prove2.me/submissions/60a8da60-127b-4273-a03f-c84f3bb6c14a

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
  have hη : 0 < η₁ := hrun.2.2.1
  have hupd := hrun.2.2.2.2.2.2.2.2.1
  set c := η₁ * (α * ε ^ p) with hc
  have hεp : 0 < ε ^ p := Real.rpow_pos_of_pos hε p
  have hc0 : 0 < c := by positivity
  have hdesc : ∀ k, f (x (k + 1)) ≤ f (x k) ∧
      (η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) →
        η₁ * (f (x k) - AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k)) ≤
          f (x k) - f (x (k + 1))) := by
    intro k
    have hden : 0 < f (x k) - AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) := by
      linarith [h26 k]
    by_cases hs : η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k)
    · have hx : x (k + 1) = x k + s k := by rw [hupd k, if_pos hs]
      have h1 : η₁ * (f (x k) - AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k)) ≤
          f (x k) - f (x (k + 1)) := by
        rw [hx]
        unfold AdaptiveCubic.Cauchy.rho at hs
        rw [le_div_iff₀ hden] at hs
        linarith
      refine ⟨?_, fun _ => h1⟩
      have : 0 < η₁ * (f (x k) - AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k)) :=
        mul_pos hη hden
      linarith
    · have hx : x (k + 1) = x k := by rw [hupd k, if_neg hs]
      exact ⟨by rw [hx], fun h => absurd h hs⟩
  have hD0 : ∀ k, 0 ≤ f (x k) - f (x (k + 1)) := fun k => by linarith [(hdesc k).1]
  have hDc : ∀ k ∈ So, c ≤ f (x k) - f (x (k + 1)) := by
    intro k hk
    have h1 := (hdesc k).2 (hSo hk).1
    have h2 := mul_le_mul_of_nonneg_left (h218 k hk) hη.le
    rw [hc]; linarith
  have hbound : ∀ T : Finset ℕ, (↑T : Set ℕ) ⊆ So → (T.card : ℝ) * c ≤ f (x 0) - flow := by
    intro T hT
    set N := T.sup id + 1
    have hTN : T ⊆ Finset.range N := by
      intro k hk
      rw [Finset.mem_range]
      have : k ≤ T.sup id := Finset.le_sup (f := id) hk
      omega
    have htel : ∑ k ∈ Finset.range N, (f (x k) - f (x (k + 1))) = f (x 0) - f (x N) :=
      Finset.sum_range_sub' (fun k => f (x k)) N
    have h1 : ∑ k ∈ T, (f (x k) - f (x (k + 1))) ≤
        ∑ k ∈ Finset.range N, (f (x k) - f (x (k + 1))) :=
      Finset.sum_le_sum_of_subset_of_nonneg hTN (fun k _ _ => hD0 k)
    have h2 : (T.card : ℝ) * c ≤ ∑ k ∈ T, (f (x k) - f (x (k + 1))) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun k hk => hDc k (hT hk)
    linarith [hflow N]
  have hfin : So.Finite := by
    by_contra hinf
    obtain ⟨M, hM⟩ := exists_nat_gt ((f (x 0) - flow) / c)
    obtain ⟨T, hT, hTc⟩ := Set.Infinite.exists_subset_card_eq hinf M
    have := hbound T hT
    rw [hTc] at this
    rw [div_lt_iff₀ hc0] at hM
    linarith
  refine ⟨hfin, ?_⟩
  have hnc : (So.ncard : ℝ) * c ≤ f (x 0) - flow := by
    have := hbound hfin.toFinset (by simp)
    rwa [Set.ncard_eq_toFinset_card So hfin]
  have hval : (f (x 0) - flow) / (η₁ * α) * ε ^ (-p) = (f (x 0) - flow) / c := by
    rw [Real.rpow_neg hε.le, hc]
    field_simp
  have hle : (So.ncard : ℝ) ≤ (f (x 0) - flow) / (η₁ * α) * ε ^ (-p) := by
    rw [hval, le_div_iff₀ hc0]; exact hnc
  have := Int.le_ceil ((f (x 0) - flow) / (η₁ * α) * ε ^ (-p))
  have h2 : ((So.ncard : ℤ) : ℝ) ≤ (⌈(f (x 0) - flow) / (η₁ * α) * ε ^ (-p)⌉ : ℝ) := by
    push_cast; linarith
  exact_mod_cast h2
