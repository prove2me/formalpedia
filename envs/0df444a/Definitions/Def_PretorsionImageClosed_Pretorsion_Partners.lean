-- Prove2me | Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
-- name    : PretorsionImageClosed_Pretorsion_Partners
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T02:28:38.872113+00:00
-- url     : https://prove2.me/theorems/889fbf7e-3c5a-42f1-8102-54f76b14bce4
-- title:
--   Partners
-- statement:
--   Definitions and structural lemmas for Partners, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
section Family
variable {ι : Type*} (F : ι → Subcategory C)
def finInf (J : Finset ι) : Subcategory C := Subcategory.iInf (fun i : J => F i)
variable {F} {T : Subcategory C} (hT : T.IsQuotientClosed) (h : ∀ i, IsPretorsionTheory T.prop (F i).prop)
include hT h
end Family
end PretorsionImageClosed.Statement


