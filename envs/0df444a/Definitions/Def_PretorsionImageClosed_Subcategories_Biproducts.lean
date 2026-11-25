-- Prove2me | Definitions.Def_PretorsionImageClosed_Subcategories_Biproducts
-- name    : PretorsionImageClosed_Subcategories_Biproducts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:34:52.637799+00:00
-- url     : https://prove2.me/theorems/f6942da3-3ae5-4b4e-8598-9ee2236aad33
-- title:
--   Biproducts
-- statement:
--   Definitions and structural lemmas for Biproducts, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Biproducts.lean

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Biproducts_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
namespace Statement.Subcategory
variable (Z : Subcategory C)
end Statement.Subcategory
end PretorsionImageClosed


