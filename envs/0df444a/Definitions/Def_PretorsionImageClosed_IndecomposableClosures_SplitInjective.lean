-- Prove2me | Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
-- name    : PretorsionImageClosed_IndecomposableClosures_SplitInjective
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T05:10:31.117729+00:00
-- url     : https://prove2.me/theorems/8b4fa128-a0a7-5a9c-83a2-9b19c724acd0
-- title:
--   Split Injective
-- statement:
--   Definitions and structural lemmas for Split Injective, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitInjective.lean

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
namespace PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
def IsRelativeSplitInjective (C : Set ι) (x : ι) : Prop :=
  ∀ P : σ.SubPresentation C (σ.obj x),
    Nonempty (SplitMono P.map)
end PretorsionImageClosed.IndecomposableSkeleton


