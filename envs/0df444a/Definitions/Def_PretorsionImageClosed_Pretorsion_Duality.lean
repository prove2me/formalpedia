-- Prove2me | Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
-- name    : PretorsionImageClosed_Pretorsion_Duality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:57:20.607856+00:00
-- url     : https://prove2.me/theorems/e6f70c3f-53f8-4cd3-93f8-4c5747187079
-- title:
--   Duality
-- statement:
--   Definitions and structural lemmas for Duality, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Theorems.Thm_PretorsionImageClosed_length_eq_of_iso
public import Theorems.Thm_PretorsionImageClosed_length_eq_zero_iff
public import Theorems.Thm_PretorsionImageClosed_length_lt_of_epi
public import Theorems.Thm_PretorsionImageClosed_length_lt_of_mono

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits Opposite
instance {C : Type*} [Category C] [Abelian C] [HasLength C] : HasLength Cᵒᵖ where
  length X := length X.unop
  length_eq_zero_iff X := (length_eq_zero_iff X.unop).trans ⟨fun h => h.op, fun h => h.unop⟩
  length_eq_of_iso e := length_eq_of_iso e.unop.symm
  length_lt_of_mono f _ hf := length_lt_of_epi f.unop (by rwa [isIso_unop_iff])
  length_lt_of_epi f _ hf := length_lt_of_mono f.unop (by rwa [isIso_unop_iff])
namespace Statement
variable {C : Type*} [Category C] [Abelian C]
theorem IsTrivial.op {Z : ObjectProperty C} {X Y : C} {f : X ⟶ Y} (h : IsTrivial Z f) :
    IsTrivial Z.op f.op := by
  obtain ⟨W, hW, g, k, hgk⟩ := h
  exact ⟨Opposite.op W, hW, k.op, g.op, by rw [← op_comp, hgk]⟩
theorem IsTrivial.unop {Z : ObjectProperty Cᵒᵖ} {X Y : Cᵒᵖ} {f : X ⟶ Y} (h : IsTrivial Z f) :
    IsTrivial Z.unop f.unop := by
  obtain ⟨W, hW, g, k, hgk⟩ := h
  exact ⟨W.unop, hW, k.unop, g.unop, by rw [← unop_comp, hgk]⟩
theorem IsPrekernel.op {Z : ObjectProperty C} {T X F : C} {u : T ⟶ X} {v : X ⟶ F}
    (h : IsPrekernel Z u v) : IsPrecokernel Z.op v.op u.op := by
  refine ⟨by rw [← op_comp]; exact h.1.op, fun {Y} v' hv' => ?_⟩
  have h' : IsTrivial Z (v'.unop ≫ v) := by
    have := hv'.unop
    rwa [unop_comp, Quiver.Hom.unop_op] at this
  obtain ⟨w, hw, hu⟩ := h.2 v'.unop h'
  refine ⟨w.op, ?_, fun w' hw' => ?_⟩
  · show u.op ≫ w.op = v'
    rw [← op_comp, hw, Quiver.Hom.op_unop]
  · have hw'' : u.op ≫ w' = v' := hw'
    apply Quiver.Hom.unop_inj
    rw [Quiver.Hom.unop_op]
    apply hu
    show w'.unop ≫ u = v'.unop
    rw [← hw'', unop_comp, Quiver.Hom.unop_op]
theorem IsPrecokernel.op {Z : ObjectProperty C} {T X F : C} {u : T ⟶ X} {v : X ⟶ F}
    (h : IsPrecokernel Z u v) : IsPrekernel Z.op v.op u.op := by
  refine ⟨by rw [← op_comp]; exact h.1.op, fun {Y} u' hu' => ?_⟩
  have h' : IsTrivial Z (u ≫ u'.unop) := by
    have := hu'.unop
    rwa [unop_comp, Quiver.Hom.unop_op] at this
  obtain ⟨w, hw, hu⟩ := h.2 u'.unop h'
  refine ⟨w.op, ?_, fun w' hw' => ?_⟩
  · show w.op ≫ v.op = u'
    rw [← op_comp, hw, Quiver.Hom.op_unop]
  · have hw'' : w' ≫ v.op = u' := hw'
    apply Quiver.Hom.unop_inj
    rw [Quiver.Hom.unop_op]
    apply hu
    show v ≫ w'.unop = u'.unop
    rw [← hw'', unop_comp, Quiver.Hom.unop_op]
theorem IsPrekernel.unop {Z : ObjectProperty Cᵒᵖ} {T X F : Cᵒᵖ} {u : T ⟶ X} {v : X ⟶ F}
    (h : IsPrekernel Z u v) : IsPrecokernel Z.unop v.unop u.unop := by
  refine ⟨by rw [← unop_comp]; exact h.1.unop, fun {Y} v' hv' => ?_⟩
  have h' : IsTrivial Z (v'.op ≫ v) := by
    have := hv'.op
    rwa [op_comp, Quiver.Hom.op_unop] at this
  obtain ⟨w, hw, hu⟩ := h.2 v'.op h'
  refine ⟨w.unop, ?_, fun w' hw' => ?_⟩
  · show u.unop ≫ w.unop = v'
    rw [← unop_comp, hw, Quiver.Hom.unop_op]
  · have hw'' : u.unop ≫ w' = v' := hw'
    apply Quiver.Hom.op_inj
    rw [Quiver.Hom.op_unop]
    apply hu
    show w'.op ≫ u = v'.op
    rw [← hw'', op_comp, Quiver.Hom.op_unop]
theorem IsPrecokernel.unop {Z : ObjectProperty Cᵒᵖ} {T X F : Cᵒᵖ} {u : T ⟶ X} {v : X ⟶ F}
    (h : IsPrecokernel Z u v) : IsPrekernel Z.unop v.unop u.unop := by
  refine ⟨by rw [← unop_comp]; exact h.1.unop, fun {Y} u' hu' => ?_⟩
  have h' : IsTrivial Z (u ≫ u'.op) := by
    have := hu'.op
    rwa [op_comp, Quiver.Hom.op_unop] at this
  obtain ⟨w, hw, hu⟩ := h.2 u'.op h'
  refine ⟨w.unop, ?_, fun w' hw' => ?_⟩
  · show w.unop ≫ v.unop = u'
    rw [← unop_comp, hw, Quiver.Hom.unop_op]
  · have hw'' : w' ≫ v.unop = u' := hw'
    apply Quiver.Hom.op_inj
    rw [Quiver.Hom.op_unop]
    apply hu
    show v ≫ w'.op = u'.op
    rw [← hw'', op_comp, Quiver.Hom.op_unop]
theorem IsPretorsionTheory.op {T F : ObjectProperty C} (h : IsPretorsionTheory T F) :
    IsPretorsionTheory F.op T.op := by
  refine ⟨fun {X Y} f hX hY => ?_, fun X => ?_⟩
  · have := (h.1 f.unop hY hX).op
    rwa [Quiver.Hom.op_unop, ObjectProperty.op_inf, inf_comm] at this
  · obtain ⟨T', F', u, v, hT', hF', hs⟩ := h.2 X.unop
    refine ⟨Opposite.op F', Opposite.op T', v.op, u.op, hF', hT', ?_⟩
    rw [inf_comm, ← ObjectProperty.op_inf]
    exact ⟨hs.2.op, hs.1.op⟩
theorem IsPretorsionTheory.unop {T F : ObjectProperty Cᵒᵖ} (h : IsPretorsionTheory T F) :
    IsPretorsionTheory F.unop T.unop := by
  refine ⟨fun {X Y} f hX hY => ?_, fun X => ?_⟩
  · have := (h.1 f.op hY hX).unop
    rwa [Quiver.Hom.unop_op, ObjectProperty.unop_inf, inf_comm] at this
  · obtain ⟨T', F', u, v, hT', hF', hs⟩ := h.2 (Opposite.op X)
    refine ⟨F'.unop, T'.unop, v.unop, u.unop, hF', hT', ?_⟩
    rw [inf_comm, ← ObjectProperty.unop_inf]
    exact ⟨hs.2.unop, hs.1.unop⟩
def Subcategory.op (Z : Subcategory C) : Subcategory Cᵒᵖ where
  prop := Z.prop.op
  prop_of_retract {X Y} h hY :=
    Z.prop_of_retract ⟨h.r.unop, h.i.unop, by rw [← unop_comp, h.retract, unop_id]⟩ hY
  prop_biprod {X Y} hX hY :=
    Z.prop_of_iso (biprod.opIso X.unop Y.unop).unop.symm (Z.prop_biprod hX hY)
  prop_of_isZero h := Z.prop_of_isZero h.unop
def Subcategory.unop (Z : Subcategory Cᵒᵖ) : Subcategory C where
  prop := Z.prop.unop
  prop_of_retract {X Y} h hY :=
    Z.prop_of_retract ⟨h.r.op, h.i.op, by rw [← op_comp, h.retract, op_id]⟩ hY
  prop_biprod {X Y} hX hY :=
    Z.prop_of_iso (biprod.opIso X Y).symm (Z.prop_biprod hX hY)
  prop_of_isZero h := Z.prop_of_isZero h.op
def PretorsionTheory.op (P : PretorsionTheory C) : PretorsionTheory Cᵒᵖ :=
  ⟨P.F.op, P.T.op, P.isPretorsionTheory.op⟩
def PretorsionTheory.unop (P : PretorsionTheory Cᵒᵖ) : PretorsionTheory C :=
  ⟨P.F.unop, P.T.unop, P.isPretorsionTheory.unop⟩
end Statement
end PretorsionImageClosed


