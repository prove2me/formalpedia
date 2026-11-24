-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_BinaryCoproductBaseChange
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_BinaryCoproductBaseChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:21.38941+00:00
-- url     : https://prove2.me/theorems/ced2531d-ff23-4307-b475-8208bed5bacf
-- title:
--   Binary Coproduct Base Change
-- statement:
--   Definitions and structural lemmas for Binary Coproduct Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/BinaryCoproductBaseChange.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_CoproductBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FunctorialResolution.EmbeddedResolution
def boolFamily (X₁ X₂ : Scheme.{u}) : ULift.{u} Bool → Scheme.{u} :=
  fun i => cond i.down X₁ X₂
def boolFamilyMap {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    ∀ i, boolFamily X₁ X₂ i ⟶ boolFamily Y₁ Y₂ i
  | ⟨true⟩ => f₁
  | ⟨false⟩ => f₂
def boolFamilyDesc {X₁ X₂ Y : Scheme.{u}} (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) :
    ∀ i, boolFamily X₁ X₂ i ⟶ Y
  | ⟨true⟩ => f₁
  | ⟨false⟩ => f₂
noncomputable def sigmaBoolFamilyInl (X₁ X₂ : Scheme.{u}) : X₁ ⟶ ∐ boolFamily X₁ X₂ :=
  Limits.Sigma.ι (boolFamily X₁ X₂) ⟨true⟩
noncomputable def sigmaBoolFamilyInr (X₁ X₂ : Scheme.{u}) : X₂ ⟶ ∐ boolFamily X₁ X₂ :=
  Limits.Sigma.ι (boolFamily X₁ X₂) ⟨false⟩
theorem pairInl_comp_desc {X₁ X₂ Y : Scheme.{u}} (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) :
    sigmaBoolFamilyInl X₁ X₂ ≫ Limits.Sigma.desc (boolFamilyDesc f₁ f₂) = f₁ :=
  Limits.Sigma.ι_desc (boolFamilyDesc f₁ f₂) ⟨true⟩
theorem pairInr_comp_desc {X₁ X₂ Y : Scheme.{u}} (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) :
    sigmaBoolFamilyInr X₁ X₂ ≫ Limits.Sigma.desc (boolFamilyDesc f₁ f₂) = f₂ :=
  Limits.Sigma.ι_desc (boolFamilyDesc f₁ f₂) ⟨false⟩
theorem sigmaPair_hom_ext {X₁ X₂ Z : Scheme.{u}} (f g : (∐ boolFamily X₁ X₂) ⟶ Z)
    (ht : sigmaBoolFamilyInl X₁ X₂ ≫ f = sigmaBoolFamilyInl X₁ X₂ ≫ g)
    (hf : sigmaBoolFamilyInr X₁ X₂ ≫ f = sigmaBoolFamilyInr X₁ X₂ ≫ g) : f = g := by
  apply Limits.Sigma.hom_ext
  rintro ⟨(_ | _)⟩
  · exact hf
  · exact ht
noncomputable def coprodIsoSigmaBoolFamily (X₁ X₂ : Scheme.{u}) : (X₁ ⨿ X₂) ≅ ∐ boolFamily X₁ X₂ where
  hom := coprod.desc (sigmaBoolFamilyInl X₁ X₂) (sigmaBoolFamilyInr X₁ X₂)
  inv := Limits.Sigma.desc (boolFamilyDesc (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) (coprod.inr : X₂ ⟶ X₁ ⨿ X₂))
  hom_inv_id := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, pairInl_comp_desc, Category.comp_id]
    · rw [coprod.inr_desc_assoc, pairInr_comp_desc, Category.comp_id]
  inv_hom_id := by
    apply sigmaPair_hom_ext
    · rw [← Category.assoc, pairInl_comp_desc, coprod.inl_desc, Category.comp_id]
    · rw [← Category.assoc, pairInr_comp_desc, coprod.inr_desc, Category.comp_id]
noncomputable def isoCoprodInitial (P : Scheme.{u}) : P ≅ P ⨿ (⊥_ Scheme.{u}) where
  hom := coprod.inl
  inv := coprod.desc (𝟙 P) (initial.to P)
  hom_inv_id := coprod.inl_desc (𝟙 P) (initial.to P)
  inv_hom_id := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc, Category.id_comp, Category.comp_id]
    · exact initial.hom_ext _ _
noncomputable def isoInitialCoprod (P : Scheme.{u}) : P ≅ (⊥_ Scheme.{u}) ⨿ P where
  hom := coprod.inr
  inv := coprod.desc (initial.to P) (𝟙 P)
  hom_inv_id := coprod.inr_desc (initial.to P) (𝟙 P)
  inv_hom_id := by
    apply coprod.hom_ext
    · exact initial.hom_ext _ _
    · rw [← Category.assoc, coprod.inr_desc, Category.id_comp, Category.comp_id]
noncomputable def isInitialOfIsEmptyScheme {X : Scheme.{u}} (h : IsEmpty X) : IsInitial X := by
  haveI := h
  exact isInitialOfIsEmpty
end FunctorialResolution.EmbeddedResolution


