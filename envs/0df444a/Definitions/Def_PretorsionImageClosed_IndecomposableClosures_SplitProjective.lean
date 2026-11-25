-- Prove2me | Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
-- name    : PretorsionImageClosed_IndecomposableClosures_SplitProjective
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T05:08:14.875102+00:00
-- url     : https://prove2.me/theorems/1e716f8e-03ba-5929-9ef7-42c8fda1a1df
-- title:
--   Split Projective
-- statement:
--   Definitions and structural lemmas for Split Projective, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/SplitProjective.lean

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
def IsRelativeSplitProjective (C : Set ι) (x : ι) : Prop :=
  ∀ P : σ.FacPresentation C (σ.obj x), IsSplitEpi P.map
namespace FacPresentation
def component
    {S : Set ι} {X : FGModuleCat.{w} R}
    (P : σ.FacPresentation S X) (t : P.index) :
    σ.obj (P.label t) ⟶ X :=
  biproduct.ι (fun t : P.index ↦ σ.obj (P.label t)) t ≫ P.map
end FacPresentation
end PretorsionImageClosed.IndecomposableSkeleton


