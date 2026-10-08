-- Prove2me | solution 1 for AffinePolicies.LargeGap.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:51:49.605988+00:00
-- url     : https://prove2.me/submissions/d1e5fd8a-3d86-4abf-9a32-7e007530092c

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting

set_option autoImplicit false

open AffinePolicies.LargeGap in
theorem lemma6_gen_mem (δ : ℝ) (m : ℕ) (σ : Equiv.Perm (Fin m)) (b : Fin m → ℝ)
    (hb : b ∈ ({0} ∪ Set.range (fun j : Fin m => (Pi.single j (1 : ℝ) : Fin m → ℝ)) ∪
      {fun _ => 1 / Real.sqrt m} ∪
      {b | ∃ S : Finset (Fin m), S.card = rr m δ ∧ b = blockPt m δ S} : Set (Fin m → ℝ))) :
    b ∘ σ ∈ ({0} ∪ Set.range (fun j : Fin m => (Pi.single j (1 : ℝ) : Fin m → ℝ)) ∪
      {fun _ => 1 / Real.sqrt m} ∪
      {b | ∃ S : Finset (Fin m), S.card = rr m δ ∧ b = blockPt m δ S} : Set (Fin m → ℝ)) := by
  rcases hb with ((h0 | ⟨j, rfl⟩) | hc) | ⟨S, hS, rfl⟩
  · rw [Set.mem_singleton_iff] at h0
    subst h0
    left; left; left; rfl
  · left; left; right
    refine ⟨σ.symm j, ?_⟩
    funext i
    simp only [Function.comp_apply, Pi.single_apply]
    by_cases h : i = σ.symm j
    · subst h; simp
    · have : σ i ≠ j := by
        intro h'; apply h; rw [← h']; simp
      simp [h, this]
  · rw [Set.mem_singleton_iff] at hc
    subst hc
    left; right; rfl
  · right
    refine ⟨S.map σ.symm.toEmbedding, by simpa using hS, ?_⟩
    funext i
    simp only [Function.comp_apply, blockPt, Finset.mem_map_equiv, Equiv.symm_symm]

open AffinePolicies.LargeGap in
theorem solution (δ : ℝ) (m : ℕ) :
    ∀ σ : Equiv.Perm (Fin m),
      c19 m ∘ σ = c19 m ∧ d19 m ∘ σ = d19 m ∧ (A19 m).submatrix σ σ = A19 m ∧
        (B19 m δ).submatrix σ σ = B19 m δ ∧ (fun b => b ∘ σ) '' U19 m δ = U19 m δ := by
  intro σ
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · funext i j; simp [A19]
  · funext i j; simp [B19, Matrix.submatrix_apply]
  · set G : Set (Fin m → ℝ) := ({0} ∪ Set.range (fun j : Fin m => (Pi.single j (1 : ℝ) : Fin m → ℝ)) ∪
      {fun _ => 1 / Real.sqrt m} ∪
      {b | ∃ S : Finset (Fin m), S.card = rr m δ ∧ b = blockPt m δ S}) with hG
    have key : ∀ τ : Equiv.Perm (Fin m), (fun b : Fin m → ℝ => b ∘ τ) '' G = G := by
      intro τ
      apply Set.Subset.antisymm
      · rintro _ ⟨b, hb, rfl⟩
        exact lemma6_gen_mem δ m τ b hb
      · intro b hb
        refine ⟨b ∘ τ.symm, lemma6_gen_mem δ m τ.symm b hb, ?_⟩
        funext i; simp
    have hU : U19 m δ = convexHull ℝ G := rfl
    have hlin : (fun b : Fin m → ℝ => b ∘ σ) = ⇑(LinearMap.funLeft ℝ ℝ σ) := rfl
    rw [hU, hlin, LinearMap.image_convexHull, ← hlin, key σ]
