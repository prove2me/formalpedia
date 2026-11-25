-- Prove2me | Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
-- name    : PretorsionImageClosed_Realizations_LeastRealization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T06:40:45.3765+00:00
-- url     : https://prove2.me/theorems/4463e4d3-e6f8-48fd-9edb-e77383d09cad
-- title:
--   Least Realization
-- statement:
--   Definitions and structural lemmas for Least Realization, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/LeastRealization.lean

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
theorem gen_op (Z : Subcategory C) (X : Cᵒᵖ) : Gen Z.op X ↔ Cogen Z X.unop :=
  ⟨fun ⟨Y, hY, p, _⟩ => ⟨Y.unop, hY, p.unop, inferInstance⟩,
    fun ⟨Y, hY, i, _⟩ => ⟨Opposite.op Y, hY, i.op, inferInstance⟩⟩
theorem cogen_op (Z : Subcategory C) (X : Cᵒᵖ) : Cogen Z.op X ↔ Gen Z X.unop :=
  ⟨fun ⟨Y, hY, i, _⟩ => ⟨Y.unop, hY, i.unop, inferInstance⟩,
    fun ⟨Y, hY, p, _⟩ => ⟨Opposite.op Y, hY, p.op, inferInstance⟩⟩
theorem Subcategory.IsImageClosed.op {Z : Subcategory C} (hZ : Z.IsImageClosed) :
    Z.op.IsImageClosed := by
  rw [isImageClosed_iff_eq_gen_inf_cogen]
  have h := (isImageClosed_iff_eq_gen_inf_cogen Z).1 hZ
  funext X
  apply propext
  show Z.prop X.unop ↔ Gen Z.op X ∧ Cogen Z.op X
  rw [gen_op, cogen_op, h, and_comm]
  rfl
variable (Z : Subcategory C) (hZ : Z.IsImageClosed)
def leastRealization : PretorsionTheory C := (greatestRealization Z.op hZ.op).unop
variable {Z}
variable (Z)
end PretorsionImageClosed.Statement


