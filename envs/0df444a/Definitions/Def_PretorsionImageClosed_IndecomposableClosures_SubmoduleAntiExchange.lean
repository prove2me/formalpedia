-- Prove2me | Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
-- name    : PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T05:09:04.104343+00:00
-- url     : https://prove2.me/theorems/771f748d-f9ce-4970-8586-9638dd3142a6
-- title:
--   Submodule Anti Exchange
-- statement:
--   Definitions and structural lemmas for Submodule Anti Exchange, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SubmoduleAntiExchange.lean

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
namespace PretorsionImageClosed.IndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
def pointReject (i : ι) (X : FGModuleCat.{w} R) :
    Submodule R X :=
  ⨅ f : X ⟶ σ.obj i, LinearMap.ker f.hom.hom
end PretorsionImageClosed.IndecomposableSkeleton


