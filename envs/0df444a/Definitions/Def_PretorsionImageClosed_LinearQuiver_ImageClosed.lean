-- Prove2me | Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
-- name    : PretorsionImageClosed_LinearQuiver_ImageClosed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T03:08:57.336345+00:00
-- url     : https://prove2.me/theorems/3a552d11-1f62-4ab9-877a-d34ea32cb623
-- title:
--   Image Closed
-- statement:
--   Definitions and structural lemmas for Image Closed, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/ImageClosed.lean

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits Statement
namespace LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
def IntersectionClosed (C : Subcategory (Statement.LinRep k n)) : Prop :=
  ∀ a b c d : Fin n, a ≤ b → c ≤ d → C.prop (interval k a b) → C.prop (interval k c d) →
    max a c ≤ min b d → C.prop (interval k (max a c) (min b d))
end LinearQuiver
end PretorsionImageClosed


