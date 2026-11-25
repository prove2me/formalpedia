-- Prove2me | Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
-- name    : PretorsionImageClosed_LinearQuiver_SummandReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T03:07:18.6775+00:00
-- url     : https://prove2.me/theorems/957ec867-1603-590f-bd13-9fe72566a310
-- title:
--   Summand Reduction
-- statement:
--   Definitions and structural lemmas for Summand Reduction, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits Statement
section Abelian
variable {C : Type*} [Category C] [Abelian C]
end Abelian
namespace LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
end LinearQuiver
end PretorsionImageClosed


