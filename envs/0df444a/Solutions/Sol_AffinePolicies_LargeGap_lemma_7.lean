-- Prove2me | solution 1 for AffinePolicies.LargeGap.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:18:42.429898+00:00
-- url     : https://prove2.me/submissions/31de9b0b-0376-4222-9c31-323e4295328c

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting

set_option autoImplicit false
open AffinePolicies.LargeGap AffinePolicies.Simplex Matrix

lemma yapl_gen_inv (δ : ℝ) (m : ℕ) (τ : Equiv.Perm (Fin m)) (g : Fin m → ℝ)
    (hg : g ∈ ({0} ∪ Set.range (fun j : Fin m => (Pi.single j (1 : ℝ) : Fin m → ℝ)) ∪
      {fun _ => 1 / Real.sqrt m} ∪
      {b | ∃ S : Finset (Fin m), S.card = rr m δ ∧ b = blockPt m δ S} : Set (Fin m → ℝ))) :
    g ∘ τ ∈ ({0} ∪ Set.range (fun j : Fin m => (Pi.single j (1 : ℝ) : Fin m → ℝ)) ∪
      {fun _ => 1 / Real.sqrt m} ∪
      {b | ∃ S : Finset (Fin m), S.card = rr m δ ∧ b = blockPt m δ S} : Set (Fin m → ℝ)) := by
  rcases hg with ((hg | hg) | hg) | hg
  · left; left; left
    have : g = 0 := hg
    subst this
    rfl
  · left; left; right
    obtain ⟨j, rfl⟩ := hg
    refine ⟨τ.symm j, ?_⟩
    funext i
    simp only [Function.comp_apply, Pi.single_apply]
    have : (i = τ.symm j) ↔ (τ i = j) := by
      constructor
      · intro h; rw [h]; simp
      · intro h; rw [← h]; simp
    by_cases h : τ i = j
    · simp [h, this.mpr h]
    · simp [h, mt this.mp h]
  · left; right
    have : g = fun _ => 1 / Real.sqrt m := hg
    subst this
    rfl
  · right
    obtain ⟨S, hS, rfl⟩ := hg
    refine ⟨S.map τ.symm.toEmbedding, by rw [Finset.card_map]; exact hS, ?_⟩
    funext i
    simp only [blockPt, Function.comp_apply]
    have : (τ i ∈ S) ↔ (i ∈ S.map τ.symm.toEmbedding) := by
      rw [Finset.mem_map_equiv]
      simp
    simp only [this]

lemma yapl_U_inv (δ : ℝ) (m : ℕ) (τ : Equiv.Perm (Fin m)) (b : Fin m → ℝ) (hb : b ∈ U19 m δ) :
    b ∘ τ ∈ U19 m δ := by
  have hconv : Convex ℝ ((LinearMap.funLeft ℝ ℝ τ) ⁻¹' (U19 m δ)) :=
    (convex_convexHull ℝ _).linear_preimage _
  have hsub : ({0} ∪ Set.range (fun j : Fin m => (Pi.single j (1 : ℝ) : Fin m → ℝ)) ∪
      {fun _ => 1 / Real.sqrt m} ∪
      {b | ∃ S : Finset (Fin m), S.card = rr m δ ∧ b = blockPt m δ S} : Set (Fin m → ℝ)) ⊆
      (LinearMap.funLeft ℝ ℝ τ) ⁻¹' (U19 m δ) := by
    intro g hg
    exact subset_convexHull ℝ _ (yapl_gen_inv δ m τ g hg)
  exact convexHull_min hsub hconv hb

lemma yapl_B_sym (δ : ℝ) (m : ℕ) (σ : Equiv.Perm (Fin m)) (y : Fin m → ℝ) :
    B19 m δ *ᵥ (y ∘ σ) = (B19 m δ *ᵥ y) ∘ σ := by
  have hB : (B19 m δ).submatrix σ σ = B19 m δ := by
    ext i j
    simp [B19, σ.injective.eq_iff]
  have := Matrix.submatrix_mulVec_equiv (B19 m δ) (y ∘ σ) σ σ
  rw [hB] at this
  have e : (y ∘ σ) ∘ σ.symm = y := by funext i; simp
  rw [e] at this
  exact this

lemma yapl_policy (m : ℕ) (σ : Equiv.Perm (Fin m)) (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ)
    (b : Fin m → ℝ) :
    affinePolicy (P.submatrix σ σ) (q ∘ σ) b = (affinePolicy P q (b ∘ σ.symm)) ∘ σ := by
  unfold affinePolicy
  rw [Matrix.submatrix_mulVec_equiv]
  rfl

lemma yapl_feas (δ : ℝ) (m : ℕ) (σ : Equiv.Perm (Fin m)) (x : Fin m → ℝ)
    (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ)
    (h : Feasible (A19 m) (B19 m δ) (U19 m δ) x (affinePolicy P q)) :
    Feasible (A19 m) (B19 m δ) (U19 m δ) x (affinePolicy (P.submatrix σ σ) (q ∘ σ)) := by
  refine ⟨h.1, fun b hb => ?_⟩
  have hb' := yapl_U_inv δ m σ.symm b hb
  obtain ⟨h1, h2⟩ := h.2 _ hb'
  rw [yapl_policy]
  refine ⟨fun i => h1 (σ i), ?_⟩
  rw [yapl_B_sym]
  intro i
  have := h2 (σ i)
  simpa [A19] using this

lemma yapl_cost (δ : ℝ) (m : ℕ) (σ : Equiv.Perm (Fin m)) (x : Fin m → ℝ)
    (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) (t : ℝ)
    (h : CostLE (c19 m) (d19 m) (U19 m δ) x (affinePolicy P q) t) :
    CostLE (c19 m) (d19 m) (U19 m δ) x (affinePolicy (P.submatrix σ σ) (q ∘ σ)) t := by
  intro b hb
  have hb' := yapl_U_inv δ m σ.symm b hb
  have := h _ hb'
  rw [yapl_policy]
  have e : d19 m ⬝ᵥ ((affinePolicy P q (b ∘ σ.symm)) ∘ σ) = d19 m ⬝ᵥ affinePolicy P q (b ∘ σ.symm) := by
    simp only [d19, dotProduct]
    exact Equiv.sum_comp σ (fun i => 1 * affinePolicy P q (b ∘ σ.symm) i)
  rw [e]
  exact this

theorem solution (δ : ℝ) (m : ℕ) (σ : Equiv.Perm (Fin m)) (x : Fin m → ℝ)
    (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ)
    (hopt : AffinePolicies.Simplex.IsOptimalAff (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) x P q) :
    AffinePolicies.Simplex.IsOptimalAff (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) x
      (P.submatrix σ σ) (q ∘ σ) := by
  refine ⟨yapl_feas δ m σ x P q hopt.1, fun x' P' q' t hf hc => ?_⟩
  have hf' := yapl_feas δ m σ.symm x' P' q' hf
  have hc' := yapl_cost δ m σ.symm x' P' q' t hc
  exact yapl_cost δ m σ x P q t (hopt.2 x' _ _ t hf' hc')
