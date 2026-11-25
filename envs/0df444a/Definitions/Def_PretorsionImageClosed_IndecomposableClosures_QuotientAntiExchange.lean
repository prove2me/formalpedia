-- Prove2me | Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
-- name    : PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T05:06:02.031835+00:00
-- url     : https://prove2.me/theorems/f8029da7-6527-4206-b67d-f6f810414b6c
-- title:
--   Quotient Anti Exchange
-- statement:
--   Definitions and structural lemmas for Quotient Anti Exchange, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/QuotientAntiExchange.lean

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
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
def pointTrace (i : ι) (X : FGModuleCat.{w} R) :
    Submodule R X :=
  ⨆ f : σ.obj i ⟶ X, LinearMap.range f.hom.hom
end PretorsionImageClosed.IndecomposableSkeleton


