-- Prove2me | Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
-- name    : PretorsionImageClosed_Realizations_TheoremA
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T03:05:33.75499+00:00
-- url     : https://prove2.me/theorems/a204f119-6bbb-4289-9eff-9305719d1996
-- title:
--   Theorem A
-- statement:
--   Definitions and structural lemmas for Theorem A, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_iff_of_iso
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_zero
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_trace_eq_top_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_of_realization
public import Theorems.Thm_PretorsionImageClosed_imageSubobject_epi_comp
public import Theorems.Thm_PretorsionImageClosed_length_eq_zero_iff
public import Theorems.Thm_PretorsionImageClosed_length_subobject_le

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits ZeroObject
namespace Statement
open Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
theorem IsImageClosed.prop_imageSubobject {Z : Subcategory C} (hZ : Z.IsImageClosed) {X N : C}
    (f : X ⟶ N) (hX : Z.prop X) (hN : Z.prop N) : Z.prop (imageSubobject f : C) :=
  Z.prop_of_iso (imageSubobjectIso f).symm (hZ f hX hN)
theorem le_gen (Z : Subcategory C) : Z.prop ≤ Gen Z := fun X hX => ⟨X, hX, 𝟙 X, inferInstance⟩
theorem le_cogen (Z : Subcategory C) : Z.prop ≤ Cogen Z := fun X hX => ⟨X, hX, 𝟙 X, inferInstance⟩
theorem gen_prop_of_epi (Z : Subcategory C) {X Y : C} (f : X ⟶ Y) [Epi f] (hX : Z.prop X) :
    Gen Z Y := ⟨X, hX, f, inferInstance⟩
theorem cogen_prop_of_mono (Z : Subcategory C) {X Y : C} (f : X ⟶ Y) [Mono f] (hY : Z.prop Y) :
    Cogen Z X := ⟨Y, hY, f, inferInstance⟩
theorem isImageClosed_iff_eq_gen_inf_cogen (Z : Subcategory C) :
    Z.IsImageClosed ↔ Z.prop = Gen Z ⊓ Cogen Z := by
  constructor
  · intro hZ
    apply le_antisymm
    · exact le_inf (le_gen Z) (le_cogen Z)
    · rintro X ⟨⟨N₁, hN₁, p, hp⟩, ⟨N₂, hN₂, i, hi⟩⟩
      -- `X` is the image of `N₁ → X → N₂`
      have : imageSubobject (p ≫ i) = imageSubobject i := imageSubobject_epi_comp p i
      have hX : Z.prop (imageSubobject (p ≫ i) : C) := hZ.prop_imageSubobject _ hN₁ hN₂
      rw [this, imageSubobject_mono] at hX
      exact Z.prop_of_iso (Subobject.underlyingIso i) hX
  · intro h X Y f hX hY
    have h1 : (Gen Z ⊓ Cogen Z) (image f) :=
      ⟨gen_prop_of_epi Z (factorThruImage f) hX, cogen_prop_of_mono Z (image.ι f) hY⟩
    rw [← h] at h1
    exact h1
variable (Z : Subcategory C) (hZ : Z.IsImageClosed)
def upperFirst : Subcategory C where
  prop X := ∀ (N : C) (f : X ⟶ N), Z.prop N → Z.prop (imageSubobject f : C)
  prop_of_retract {X Y} h hY := by
    intro N f hN
    rw [← imageSubobject_epi_comp h.r f]
    exact hY _ (h.r ≫ f) hN
  prop_biprod {X Y} hX hY := by
    intro N f hN
    -- `f = biprod.map e₁ e₂ ≫ biprod.desc ι₁ ι₂` with `eᵢ` epi onto the images
    have hfac : f = biprod.map (factorThruImageSubobject (biprod.inl ≫ f))
        (factorThruImageSubobject (biprod.inr ≫ f)) ≫
        biprod.desc (imageSubobject (biprod.inl ≫ f)).arrow
          (imageSubobject (biprod.inr ≫ f)).arrow := by
      apply biprod.hom_ext'
      · rw [biprod.inl_map_assoc, biprod.inl_desc, imageSubobject_arrow_comp]
      · rw [biprod.inr_map_assoc, biprod.inr_desc, imageSubobject_arrow_comp]
    rw [hfac, imageSubobject_epi_comp]
    exact hZ.prop_imageSubobject _ (Z.prop_biprod (hX _ _ hN) (hY _ _ hN)) hN
  prop_of_isZero {X} hX := by
    intro N f hN
    rw [hX.eq_zero_of_src f, imageSubobject_zero]
    exact Z.prop_of_iso Subobject.botCoeIsoZero.symm Z.prop_zero
theorem upperFirst_isQuotientClosed : (upperFirst Z hZ).IsQuotientClosed := by
  intro X Y q hq hX N f hN
  rw [← imageSubobject_epi_comp q f]
  exact hX _ (q ≫ f) hN
theorem le_upperFirst : Z.prop ≤ (upperFirst Z hZ).prop := fun X hX N f hN =>
  hZ.prop_imageSubobject f hX hN
theorem upperFirst_inf_cogen : (upperFirst Z hZ).prop ⊓ Cogen Z = Z.prop := by
  apply le_antisymm
  · rintro X ⟨hX, N, hN, i, hi⟩
    have := hX _ i hN
    rwa [imageSubobject_mono, Z.prop_iff_of_iso (Subobject.underlyingIso i)] at this
  · exact le_inf (le_upperFirst Z hZ) (le_cogen Z)
theorem cogen_le_lowerSecond_aux {Y : C} (hY : Cogen Z Y) :
    Z.prop ((upperFirst Z hZ).trace Y : C) := by
  rw [← upperFirst_inf_cogen Z hZ]
  obtain ⟨N, hN, i, hi⟩ := hY
  exact ⟨(upperFirst Z hZ).prop_trace Y, N, hN, ((upperFirst Z hZ).trace Y).arrow ≫ i, inferInstance⟩
def lowerSecond : Subcategory C where
  prop Y := Z.prop ((upperFirst Z hZ).trace Y : C)
  prop_of_retract h hY :=
    Z.prop_of_retract (traceRetract (upperFirst_isQuotientClosed Z hZ) h) hY
  prop_biprod hX hY :=
    Z.prop_of_iso (traceBiprodIso (upperFirst_isQuotientClosed Z hZ) _ _).symm (Z.prop_biprod hX hY)
  prop_of_isZero {X} hX := by
    apply Z.prop_of_isZero
    rw [← length_eq_zero_iff]
    have := length_subobject_le ((upperFirst Z hZ).trace X)
    rw [(length_eq_zero_iff X).2 hX] at this
    omega
theorem lowerSecond_prop_iff (Y : C) :
    (lowerSecond Z hZ).prop Y ↔ Z.prop ((upperFirst Z hZ).trace Y : C) := Iff.rfl
theorem lowerSecond_isSubobjectClosed : (lowerSecond Z hZ).IsSubobjectClosed := by
  intro W Y i hi hY
  have hT : (upperFirst Z hZ).IsQuotientClosed := upperFirst_isQuotientClosed Z hZ
  -- `t(W) → t(Y)` is a monomorphism into an object of `Z`
  have hmono : Mono (traceMap hT i) := by
    have : Mono (traceMap hT i ≫ ((upperFirst Z hZ).trace Y).arrow) := by
      rw [traceMap_arrow]
      exact mono_comp _ _
    exact mono_of_mono _ ((upperFirst Z hZ).trace Y).arrow
  change Z.prop ((upperFirst Z hZ).trace W : C)
  rw [← upperFirst_inf_cogen Z hZ]
  exact ⟨(upperFirst Z hZ).prop_trace W, _, hY, traceMap hT i, hmono⟩
theorem cogen_le_lowerSecond : Cogen Z ≤ (lowerSecond Z hZ).prop := fun _ hY =>
  cogen_le_lowerSecond_aux Z hZ hY
theorem le_lowerSecond : Z.prop ≤ (lowerSecond Z hZ).prop := fun Y hY =>
  cogen_le_lowerSecond Z hZ Y (le_cogen Z Y hY)
theorem upperFirst_inf_lowerSecond : (upperFirst Z hZ).prop ⊓ (lowerSecond Z hZ).prop = Z.prop := by
  apply le_antisymm
  · rintro X ⟨hX, hX'⟩
    have ht := (trace_eq_top_iff (upperFirst_isQuotientClosed Z hZ)).2 hX
    rw [lowerSecond_prop_iff, ht] at hX'
    exact Z.prop_of_iso (asIso (⊤ : Subobject X).arrow) hX'
  · exact le_inf (le_upperFirst Z hZ) (le_lowerSecond Z hZ)
theorem isPretorsionTheory_upperFirst_lowerSecond :
    IsPretorsionTheory (upperFirst Z hZ).prop (lowerSecond Z hZ).prop := by
  have hT : (upperFirst Z hZ).IsQuotientClosed := upperFirst_isQuotientClosed Z hZ
  have hF : (lowerSecond Z hZ).IsSubobjectClosed := lowerSecond_isSubobjectClosed Z hZ
  have hinf := upperFirst_inf_lowerSecond Z hZ
  apply isPretorsionTheory_of_realization hT hF
  · intro Y
    rw [hinf]
    exact Iff.rfl
  · intro E
    rw [hinf]
    constructor
    · intro hE Y f hY
      exact ⟨_, hY, ((upperFirst Z hZ).trace Y).factorThru f (trace_factors hT f hE), _,
        Subobject.factorThru_arrow _ _ _⟩
    · intro h N f hN
      -- the image `I` of `f` lies in `Cogen Z ⊆ F⁻(Z)`, so `E → I` is `Z`-trivial
      have hI : (lowerSecond Z hZ).prop (imageSubobject f : C) :=
        cogen_le_lowerSecond Z hZ _ (cogen_prop_of_mono Z (imageSubobject f).arrow hN)
      obtain ⟨M, hM, a, b, hab⟩ := h (factorThruImageSubobject f) hI
      have hb : Epi b := epi_of_epi_fac hab
      have hgen : Gen Z (imageSubobject f : C) := gen_prop_of_epi Z b hM
      have hcogen : Cogen Z (imageSubobject f : C) := cogen_prop_of_mono Z (imageSubobject f).arrow hN
      have heq := (isImageClosed_iff_eq_gen_inf_cogen Z).1 hZ
      rw [heq]
      exact ⟨hgen, hcogen⟩
def greatestRealization : PretorsionTheory C where
  T := upperFirst Z hZ
  F := lowerSecond Z hZ
  isPretorsionTheory := isPretorsionTheory_upperFirst_lowerSecond Z hZ
variable {Z hZ}
section Greatest
variable (hZ : Z.IsImageClosed) (P : PretorsionTheory C) (hP : P.middle = Z.prop)
include hP
end Greatest
end Statement
end PretorsionImageClosed


