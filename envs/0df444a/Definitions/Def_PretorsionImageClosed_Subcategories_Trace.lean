-- Prove2me | Definitions.Def_PretorsionImageClosed_Subcategories_Trace
-- name    : PretorsionImageClosed_Subcategories_Trace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T02:25:36.235277+00:00
-- url     : https://prove2.me/theorems/0a77b454-72bb-49b2-8cfe-7e2a73099565
-- title:
--   Trace
-- statement:
--   Definitions and structural lemmas for Trace, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_zero
public import Theorems.Thm_PretorsionImageClosed_Subobject_exists_maximal_of_nonempty
public import Theorems.Thm_PretorsionImageClosed_Subobject_exists_minimal_of_nonempty

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [Abelian C]
def sumSubobject {X : C} (S S' : Subobject X) : Subobject X :=
  imageSubobject (biprod.desc S.arrow S'.arrow)
theorem le_sumSubobject_left {X : C} (S S' : Subobject X) : S ≤ sumSubobject S S' :=
  Subobject.le_of_factors (by
    rw [← biprod.inl_desc S.arrow S'.arrow]
    exact imageSubobject_factors_comp_self _ _)
theorem le_sumSubobject_right {X : C} (S S' : Subobject X) : S' ≤ sumSubobject S S' :=
  Subobject.le_of_factors (by
    rw [← biprod.inr_desc S.arrow S'.arrow]
    exact imageSubobject_factors_comp_self _ _)
namespace Statement.Subcategory
variable (T : Subcategory C) (X : C)
def subobjectsIn : Set (Subobject X) := {S | T.prop (S : C)}
theorem bot_mem_subobjectsIn : ⊥ ∈ T.subobjectsIn X :=
  T.prop_of_iso Subobject.botCoeIsoZero.symm T.prop_zero
theorem prop_sumSubobject (hT : T.IsQuotientClosed) {S S' : Subobject X} (hS : T.prop (S : C))
    (hS' : T.prop (S' : C)) : T.prop (sumSubobject S S' : C) :=
  T.prop_of_iso (imageSubobjectIso _).symm
    (hT (factorThruImage (biprod.desc S.arrow S'.arrow)) inferInstance (T.prop_biprod hS hS'))
variable (F : Subcategory C)
def quotientsIn : Set (Subobject X) := {K | F.prop (cokernel K.arrow)}
theorem top_mem_quotientsIn : ⊤ ∈ F.quotientsIn X :=
  F.prop_of_iso (cokernel.ofEpi (⊤ : Subobject X).arrow).symm F.prop_zero
variable [HasLength C]
def trace : Subobject X :=
  Classical.choose
    (Subobject.exists_maximal_of_nonempty (T.subobjectsIn X) ⟨⊥, T.bot_mem_subobjectsIn X⟩)
theorem trace_spec :
    T.trace X ∈ T.subobjectsIn X ∧
      ∀ S ∈ T.subobjectsIn X, T.trace X ≤ S → T.trace X = S :=
  Classical.choose_spec
    (Subobject.exists_maximal_of_nonempty (T.subobjectsIn X) ⟨⊥, T.bot_mem_subobjectsIn X⟩)
theorem prop_trace : T.prop (T.trace X : C) := (T.trace_spec X).1
theorem trace_maximal {S : Subobject X} (hS : T.prop (S : C)) (h : T.trace X ≤ S) :
    T.trace X = S :=
  (T.trace_spec X).2 S hS h
variable {T X}
theorem le_trace (hT : T.IsQuotientClosed) {S : Subobject X} (hS : T.prop (S : C)) :
    S ≤ T.trace X := by
  have hmem : T.prop (sumSubobject (T.trace X) S : C) :=
    T.prop_sumSubobject X hT (T.prop_trace X) hS
  rw [T.trace_maximal X hmem (le_sumSubobject_left _ _)]
  exact le_sumSubobject_right _ _
theorem trace_factors (hT : T.IsQuotientClosed) {Y : C} (f : Y ⟶ X) (hY : T.prop Y) :
    (T.trace X).Factors f := by
  have himg : T.prop (imageSubobject f : C) :=
    T.prop_of_iso (imageSubobjectIso f).symm (hT (factorThruImage f) inferInstance hY)
  exact Subobject.factors_of_le f (le_trace hT himg)
    ((Subobject.factors_iff _ _).2 ⟨factorThruImageSubobject f, imageSubobject_arrow_comp f⟩)
def traceMap (hT : T.IsQuotientClosed) {W X : C} (f : W ⟶ X) :
    (T.trace W : C) ⟶ (T.trace X : C) :=
  (T.trace X).factorThru ((T.trace W).arrow ≫ f) (trace_factors hT _ (T.prop_trace W))
@[reassoc (attr := simp)]
theorem traceMap_arrow (hT : T.IsQuotientClosed) {W X : C} (f : W ⟶ X) :
    traceMap hT f ≫ (T.trace X).arrow = (T.trace W).arrow ≫ f :=
  Subobject.factorThru_arrow _ _ _
theorem traceMap_id (hT : T.IsQuotientClosed) (X : C) : traceMap hT (𝟙 X) = 𝟙 _ := by
  rw [← cancel_mono (T.trace X).arrow, traceMap_arrow, Category.comp_id, Category.id_comp]
theorem traceMap_comp (hT : T.IsQuotientClosed) {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) :
    traceMap hT (f ≫ g) = traceMap hT f ≫ traceMap hT g := by
  rw [← cancel_mono (T.trace Y).arrow, traceMap_arrow, Category.assoc, traceMap_arrow,
    traceMap_arrow_assoc]
def traceRetract (hT : T.IsQuotientClosed) {W X : C} (h : Retract W X) :
    Retract (T.trace W : C) (T.trace X : C) where
  i := traceMap hT h.i
  r := traceMap hT h.r
  retract := by rw [← traceMap_comp, h.retract, traceMap_id]
theorem trace_biprod (hT : T.IsQuotientClosed) (Y₁ Y₂ : C) :
    T.trace (Y₁ ⊞ Y₂) = Subobject.mk (biprod.map (T.trace Y₁).arrow (T.trace Y₂).arrow) := by
  apply le_antisymm
  · have h1 := trace_factors hT ((T.trace (Y₁ ⊞ Y₂)).arrow ≫ biprod.fst) (T.prop_trace _)
    have h2 := trace_factors hT ((T.trace (Y₁ ⊞ Y₂)).arrow ≫ biprod.snd) (T.prop_trace _)
    refine Subobject.le_mk_of_comm
      (biprod.lift ((T.trace Y₁).factorThru _ h1) ((T.trace Y₂).factorThru _ h2)) ?_
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, Subobject.factorThru_arrow]
    · rw [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, Subobject.factorThru_arrow]
  · exact le_trace hT (T.prop_of_iso (Subobject.underlyingIso _).symm
      (T.prop_biprod (T.prop_trace Y₁) (T.prop_trace Y₂)))
def traceBiprodIso (hT : T.IsQuotientClosed) (Y₁ Y₂ : C) :
    (T.trace (Y₁ ⊞ Y₂) : C) ≅ (T.trace Y₁ : C) ⊞ (T.trace Y₂ : C) :=
  (Subobject.isoOfEq _ _ (trace_biprod hT Y₁ Y₂)).trans (Subobject.underlyingIso _)
variable (X)
def reject : Subobject X :=
  Classical.choose
    (Subobject.exists_minimal_of_nonempty (F.quotientsIn X) ⟨⊤, F.top_mem_quotientsIn X⟩)
variable {F X}
end Statement.Subcategory
end PretorsionImageClosed
namespace PretorsionImageClosed.Statement.Subcategory
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C}
end PretorsionImageClosed.Statement.Subcategory


