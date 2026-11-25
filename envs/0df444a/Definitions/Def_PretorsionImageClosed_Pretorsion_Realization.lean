-- Prove2me | Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
-- name    : PretorsionImageClosed_Pretorsion_Realization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T02:27:11.655976+00:00
-- url     : https://prove2.me/theorems/9707b0a7-9a60-4c77-a54d-7a47ddc2cc24
-- title:
--   Realization
-- statement:
--   Definitions and structural lemmas for Realization, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Realization.lean

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits ZeroObject
namespace Statement
open Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C}
end Statement
end PretorsionImageClosed


