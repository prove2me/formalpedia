-- Prove2me | solution 1 for AffinePolicies.LargeGap.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:48:04.131913+00:00
-- url     : https://prove2.me/submissions/bc4f959f-3367-46e1-9bba-78eec488a177

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting

set_option autoImplicit false

open AffinePolicies.LargeGap in
theorem e38a7ff4_fwd (δ : ℝ) (m : ℕ) (τ : Equiv.Perm (Fin m))
    (x : Fin m → ℝ) (hx : x ∈ U19 m δ) : x ∘ τ ∈ U19 m δ := by
  unfold U19 at hx ⊢
  set S : Set (Fin m → ℝ) := ({0} ∪ Set.range (fun j : Fin m => (Pi.single j (1 : ℝ) : Fin m → ℝ)) ∪
    {fun _ => 1 / Real.sqrt m} ∪
    {b | ∃ S : Finset (Fin m), S.card = rr m δ ∧ b = blockPt m δ S}) with hS
  let f : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) := LinearMap.funLeft ℝ ℝ τ
  have hfS : f '' S ⊆ S := by
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ((hy | ⟨j, rfl⟩) | hy) | ⟨T, hT, rfl⟩
    · left; left; left
      rw [Set.mem_singleton_iff] at hy ⊢
      subst hy
      rfl
    · left; left; right
      refine ⟨τ⁻¹ j, ?_⟩
      funext i
      show (Pi.single (τ⁻¹ j) (1:ℝ) : Fin m → ℝ) i = (Pi.single j (1:ℝ) : Fin m → ℝ) (τ i)
      by_cases h : i = τ⁻¹ j
      · subst h; simp
      · have h2 : τ i ≠ j := by
          intro h3; apply h; rw [← h3]; simp
        rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h2]
    · left; right
      rw [Set.mem_singleton_iff] at hy ⊢
      subst hy
      rfl
    · right
      refine ⟨T.map τ.symm.toEmbedding, by rw [Finset.card_map]; exact hT, ?_⟩
      funext i
      show blockPt m δ T (τ i) = blockPt m δ (T.map τ.symm.toEmbedding) i
      simp only [blockPt]
      apply if_congr _ rfl rfl
      simp only [Finset.mem_map_equiv, Equiv.symm_symm]
  have : f x ∈ f '' convexHull ℝ S := ⟨x, hx, rfl⟩
  rw [LinearMap.image_convexHull] at this
  exact convexHull_mono hfS this

open AffinePolicies.LargeGap in
theorem solution (δ : ℝ) (m : ℕ) :
    ∀ σ : Equiv.Perm (Fin m), AffinePolicies.TwoGap.IsPermInvariant (U19 m δ) σ := by
  intro τ x
  constructor
  · exact e38a7ff4_fwd δ m τ x
  · intro h
    have := e38a7ff4_fwd δ m τ⁻¹ (x ∘ τ) h
    have e : (x ∘ τ) ∘ ⇑τ⁻¹ = x := by
      funext i; simp
    rwa [e] at this
