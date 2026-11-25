-- Prove2me | Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
-- name    : PretorsionImageClosed_Subobjects_Quotients
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:30:35.497369+00:00
-- url     : https://prove2.me/theorems/afebe6e1-1c17-4f69-95e6-74552d52befa
-- title:
--   Quotients
-- statement:
--   Definitions and structural lemmas for Quotients, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Quotients.lean

module
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]
theorem exact_kernelSubobject_arrow {X Q : C} (π : X ⟶ Q) :
    (ShortComplex.mk (kernelSubobject π).arrow π (kernelSubobject_arrow_comp π)).Exact := by
  rw [ShortComplex.exact_iff_image_eq_kernel]
  change imageSubobject (kernelSubobject π).arrow = kernelSubobject π
  rw [imageSubobject_mono, Subobject.mk_arrow]
instance mono_cokernelDesc_kernelSubobject_arrow {X Q : C} (π : X ⟶ Q) :
    Mono (cokernel.desc (kernelSubobject π).arrow π (kernelSubobject_arrow_comp π)) :=
  (exact_kernelSubobject_arrow π).mono_cokernelDesc
instance epi_cokernelDesc_kernelSubobject_arrow {X Q : C} (π : X ⟶ Q) [Epi π] :
    Epi (cokernel.desc (kernelSubobject π).arrow π (kernelSubobject_arrow_comp π)) :=
  epi_of_epi_fac (cokernel.π_desc _ _ _)
def cokernelKernelSubobjectArrowIso {X Q : C} (π : X ⟶ Q) [Epi π] :
    cokernel (kernelSubobject π).arrow ≅ Q :=
  haveI : IsIso (cokernel.desc (kernelSubobject π).arrow π (kernelSubobject_arrow_comp π)) :=
    isIso_of_mono_of_epi _
  asIso (cokernel.desc (kernelSubobject π).arrow π (kernelSubobject_arrow_comp π))
end PretorsionImageClosed


