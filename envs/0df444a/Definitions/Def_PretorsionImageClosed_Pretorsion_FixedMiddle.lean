-- Prove2me | Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
-- name    : PretorsionImageClosed_Pretorsion_FixedMiddle
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T06:36:54.394749+00:00
-- url     : https://prove2.me/theorems/07bea2d0-85bb-4ebd-9cab-6409427b03e1
-- title:
--   Fixed Middle
-- statement:
--   Definitions and structural lemmas for Fixed Middle, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/FixedMiddle.lean

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
namespace PretorsionTheory
variable (S : Set (PretorsionTheory C)) (Z : Subcategory C)
theorem isQuotientClosed_meetT : (meetT S).IsQuotientClosed :=
  IsQuotientClosed.iInf fun P : S => P.1.isPretorsionTheory.isQuotientClosed
def fixedF : Subcategory C where
  prop Y := Z.prop ((meetT S).trace Y : C)
  prop_of_retract h hY := Z.prop_of_retract (traceRetract (isQuotientClosed_meetT S) h) hY
  prop_biprod hX hY :=
    Z.prop_of_iso (traceBiprodIso (isQuotientClosed_meetT S) _ _).symm (Z.prop_biprod hX hY)
  prop_of_isZero h := Z.prop_of_isZero (IsZero.of_mono ((meetT S).trace _).arrow h)
variable {S Z} {P₀ : PretorsionTheory C} (hP₀ : P₀ ∈ S) (hS : ∀ P ∈ S, P.middle = Z.prop)
include hP₀ hS
end PretorsionTheory
end PretorsionImageClosed.Statement


