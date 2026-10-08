-- Prove2me | solution 1 for ApproxCliqueWidth.Certificate.rank_submatrix_submodular
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T17:06:50.637992+00:00
-- url     : https://prove2.me/submissions/1876ab4e-d6a3-429b-aedd-b9089fe846fa

import Mathlib

set_option autoImplicit false

namespace RSSubA747

open Module

variable {F R C : Type*} [Field F] [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

noncomputable def proj (F : Type*) [Field F] (Y : Finset C) : (C → F) →ₗ[F] (↥Y → F) :=
  LinearMap.funLeft F F (fun j : ↥Y => (j : C))

noncomputable def V (M : Matrix R C F) (X : Finset R) : Submodule F (C → F) :=
  Submodule.span F (M.row '' (X : Set R))

lemma key_finrank {E G : Type*} [AddCommGroup E] [Module F E] [FiniteDimensional F E]
    [AddCommGroup G] [Module F G] (π : E →ₗ[F] G) (W : Submodule F E)
    (h : LinearMap.ker π ≤ W) :
    finrank F (W.map π) + finrank F (LinearMap.ker π) = finrank F W := by
  have := LinearMap.finrank_range_add_finrank_ker (π.domRestrict W)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at this
  rw [← this, (Submodule.comapSubtypeEquivOfLe h).finrank_eq]

lemma mem_ker_proj (Y : Finset C) (v : C → F) :
    v ∈ LinearMap.ker (proj F Y) ↔ ∀ j ∈ Y, v j = 0 := by
  rw [LinearMap.mem_ker, funext_iff]
  simp [proj, LinearMap.funLeft_apply]

lemma rank_sub (M : Matrix R C F) (X : Finset R) (Y : Finset C) :
    (M.submatrix (fun i : ↥X => (i : R)) (fun j : ↥Y => (j : C))).rank
      + finrank F (LinearMap.ker (proj F Y)) = finrank F ↥(V M X ⊔ LinearMap.ker (proj F Y) : Submodule F (C → F)) := by
  rw [← key_finrank (proj F Y) _ le_sup_right, Submodule.map_sup]
  have h0 : (LinearMap.ker (proj F Y)).map (proj F Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  have hs : Set.range (M.submatrix (fun i : ↥X => (i : R)) (fun j : ↥Y => (j : C))).row
      = (proj F Y) '' (M.row '' (X : Set R)) := by
    ext w
    simp only [Set.mem_range, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨M.row i, ⟨i, i.2, rfl⟩, ?_⟩
      ext j; simp [proj, LinearMap.funLeft_apply, Matrix.row]
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      refine ⟨⟨i, hi⟩, ?_⟩
      ext j; simp [proj, LinearMap.funLeft_apply, Matrix.row]
  rw [h0, sup_bot_eq, Matrix.rank_eq_finrank_span_row, V, Submodule.map_span, hs]


lemma ker_union (Y₁ Y₂ : Finset C) :
    LinearMap.ker (proj F (Y₁ ∪ Y₂)) = LinearMap.ker (proj F Y₁) ⊓ LinearMap.ker (proj F Y₂) := by
  ext v
  simp only [Submodule.mem_inf, mem_ker_proj, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩
  · rintro ⟨h1, h2⟩ j (hj | hj)
    · exact h1 j hj
    · exact h2 j hj

lemma ker_inter (Y₁ Y₂ : Finset C) :
    LinearMap.ker (proj F (Y₁ ∩ Y₂)) = LinearMap.ker (proj F Y₁) ⊔ LinearMap.ker (proj F Y₂) := by
  apply le_antisymm
  · intro v hv
    rw [mem_ker_proj] at hv
    rw [Submodule.mem_sup]
    refine ⟨fun j => if j ∈ Y₁ then 0 else v j, ?_, fun j => if j ∈ Y₁ then v j else 0, ?_, ?_⟩
    · rw [mem_ker_proj]; intro j hj; simp [hj]
    · rw [mem_ker_proj]; intro j hj
      by_cases h1 : j ∈ Y₁
      · simp [h1, hv j (Finset.mem_inter.2 ⟨h1, hj⟩)]
      · simp [h1]
    · ext j; by_cases h1 : j ∈ Y₁ <;> simp [h1]
  · apply sup_le
    · intro v hv; rw [mem_ker_proj] at hv ⊢
      intro j hj; exact hv j (Finset.mem_inter.1 hj).1
    · intro v hv; rw [mem_ker_proj] at hv ⊢
      intro j hj; exact hv j (Finset.mem_inter.1 hj).2

lemma V_union (M : Matrix R C F) (X₁ X₂ : Finset R) : V M (X₁ ∪ X₂) = V M X₁ ⊔ V M X₂ := by
  simp only [V, Finset.coe_union, Set.image_union, Submodule.span_union]

lemma V_inter (M : Matrix R C F) (X₁ X₂ : Finset R) : V M (X₁ ∩ X₂) ≤ V M X₁ ⊓ V M X₂ := by
  apply le_inf <;> apply Submodule.span_mono <;> apply Set.image_mono <;> simp

theorem main (M : Matrix R C F) (X₁ X₂ : Finset R) (Y₁ Y₂ : Finset C) :
    (M.submatrix (fun i : ↥(X₁ ∪ X₂) => (i : R)) (fun j : ↥(Y₁ ∩ Y₂) => (j : C))).rank +
        (M.submatrix (fun i : ↥(X₁ ∩ X₂) => (i : R)) (fun j : ↥(Y₁ ∪ Y₂) => (j : C))).rank ≤
      (M.submatrix (fun i : ↥X₁ => (i : R)) (fun j : ↥Y₁ => (j : C))).rank +
        (M.submatrix (fun i : ↥X₂ => (i : R)) (fun j : ↥Y₂ => (j : C))).rank := by
  have e1 := rank_sub M (X₁ ∪ X₂) (Y₁ ∩ Y₂)
  have e2 := rank_sub M (X₁ ∩ X₂) (Y₁ ∪ Y₂)
  have e3 := rank_sub M X₁ Y₁
  have e4 := rank_sub M X₂ Y₂
  rw [ker_inter, V_union] at e1
  rw [ker_union] at e2
  set K₁ := LinearMap.ker (proj F Y₁)
  set K₂ := LinearMap.ker (proj F Y₂)
  have hA : V M X₁ ⊔ K₁ ⊔ V M X₂ ⊔ K₂ = (V M X₁ ⊔ K₁) ⊔ (V M X₂ ⊔ K₂) := by
    simp only [sup_assoc]
  have hU : V M X₁ ⊔ V M X₂ ⊔ (K₁ ⊔ K₂) = (V M X₁ ⊔ K₁) ⊔ (V M X₂ ⊔ K₂) := by
    rw [sup_sup_sup_comm]
  rw [hU] at e1
  have hle : V M (X₁ ∩ X₂) ⊔ K₁ ⊓ K₂ ≤ (V M X₁ ⊔ K₁) ⊓ (V M X₂ ⊔ K₂) := by
    apply sup_le
    · exact le_trans (V_inter M X₁ X₂) (inf_le_inf le_sup_left le_sup_left)
    · exact inf_le_inf le_sup_right le_sup_right
  have hm := Submodule.finrank_mono hle
  have hAB := Submodule.finrank_sup_add_finrank_inf_eq (V M X₁ ⊔ K₁) (V M X₂ ⊔ K₂)
  have hK := Submodule.finrank_sup_add_finrank_inf_eq K₁ K₂
  omega

end RSSubA747

theorem solution {F R C : Type*} [Field F] [Fintype R] [Fintype C]
    [DecidableEq R] [DecidableEq C] (M : Matrix R C F) (X₁ X₂ : Finset R) (Y₁ Y₂ : Finset C) :
    (M.submatrix (fun i : ↥(X₁ ∪ X₂) => (i : R)) (fun j : ↥(Y₁ ∩ Y₂) => (j : C))).rank +
        (M.submatrix (fun i : ↥(X₁ ∩ X₂) => (i : R)) (fun j : ↥(Y₁ ∪ Y₂) => (j : C))).rank ≤
      (M.submatrix (fun i : ↥X₁ => (i : R)) (fun j : ↥Y₁ => (j : C))).rank +
        (M.submatrix (fun i : ↥X₂ => (i : R)) (fun j : ↥Y₂ => (j : C))).rank := by
  exact RSSubA747.main M X₁ X₂ Y₁ Y₂
