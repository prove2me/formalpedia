-- Prove2me | solution 1 for AffinePolicies.TwoGap.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:45:53.510682+00:00
-- url     : https://prove2.me/submissions/42b10d7c-4adf-4047-b450-208c730f8f4a

import Mathlib
import Definitions.Def_AffinePolicies_TwoGap_Setting

set_option autoImplicit false

open AffinePolicies.TwoGap in
theorem lemma2_aux_inv (m : ℕ) (τ : Equiv.Perm (Fin m)) (hτ : τ ∈ Gamma m) :
    τ⁻¹ ∈ Gamma m := by
  intro i
  have := hτ (τ⁻¹ i)
  simpa using this.symm

open AffinePolicies.TwoGap in
theorem lemma2_aux_fwd (m : ℕ) (τ : Equiv.Perm (Fin m)) (hτ : τ ∈ Gamma m)
    (x : Fin m → ℝ) (hx : x ∈ U6 m) : x ∘ τ ∈ U6 m := by
  unfold U6 at hx ⊢
  set S : Set (Fin m → ℝ) := ({0} ∪ Set.range (fun j : Fin m => (Pi.single j (1 : ℝ) : Fin m → ℝ)) ∪
    {bLow m, bHigh m}) with hS
  let f : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) := LinearMap.funLeft ℝ ℝ τ
  have hfS : f '' S ⊆ S := by
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with (hy | ⟨j, rfl⟩) | hy
    · left; left
      rw [Set.mem_singleton_iff] at hy ⊢
      subst hy
      rfl
    · left; right
      refine ⟨τ⁻¹ j, ?_⟩
      funext i
      show (Pi.single (τ⁻¹ j) (1:ℝ) : Fin m → ℝ) i = (Pi.single j (1:ℝ) : Fin m → ℝ) (τ i)
      by_cases h : i = τ⁻¹ j
      · subst h; simp
      · have h2 : τ i ≠ j := by
          intro h3; apply h; rw [← h3]; simp
        rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h2]
    · right
      rcases hy with rfl | rfl
      · left
        funext i
        show bLow m (τ i) = bLow m i
        simp only [bLow]
        exact if_congr (hτ i).symm rfl rfl
      · right
        funext i
        show bHigh m (τ i) = bHigh m i
        simp only [bHigh]
        have := hτ i
        have e : (m / 2 ≤ ((τ i : Fin m) : ℕ)) ↔ (m / 2 ≤ (i : ℕ)) := by
          rw [← not_lt, ← not_lt, this]
        exact if_congr e rfl rfl
  have : f x ∈ f '' convexHull ℝ S := ⟨x, hx, rfl⟩
  rw [LinearMap.image_convexHull] at this
  exact convexHull_mono hfS this

open AffinePolicies.TwoGap in
theorem solution (m : ℕ) (hm_even : Even m) :
    ∀ τ ∈ Gamma m, IsPermInvariant (U6 m) τ := by
  intro τ hτ x
  constructor
  · exact lemma2_aux_fwd m τ hτ x
  · intro h
    have := lemma2_aux_fwd m τ⁻¹ (lemma2_aux_inv m τ hτ) (x ∘ τ) h
    have e : (x ∘ τ) ∘ ⇑τ⁻¹ = x := by
      funext i; simp
    rwa [e] at this
