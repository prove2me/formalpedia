-- Prove2me | Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
-- name    : PretorsionImageClosed_Pretorsion_Criterion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T02:27:19.140358+00:00
-- url     : https://prove2.me/theorems/39111615-f84a-4df0-b845-08be28493849
-- title:
--   Criterion
-- statement:
--   Definitions and structural lemmas for Criterion, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Criterion.lean

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C} {X : C}
end PretorsionImageClosed.Statement


