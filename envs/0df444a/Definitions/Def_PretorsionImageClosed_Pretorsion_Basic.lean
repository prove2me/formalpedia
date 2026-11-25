-- Prove2me | Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
-- name    : PretorsionImageClosed_Pretorsion_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:34:45.147447+00:00
-- url     : https://prove2.me/theorems/10d4c36e-2c9d-472d-9f70-743ba8d7b52f
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits ZeroObject
namespace Statement
variable {C : Type*} [Category C] {Z : ObjectProperty C}
section Components
variable [HasZeroMorphisms C] [HasBinaryBiproducts C] [Balanced C]
end Components
end Statement
end PretorsionImageClosed


