-- Prove2me | Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Skeleton
-- name    : PretorsionImageClosed_IndecomposableClosures_Skeleton
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:34:01.829379+00:00
-- url     : https://prove2.me/theorems/6e0de762-74c8-49d5-96cd-d5cca333d08a
-- title:
--   Skeleton
-- statement:
--   Definitions and structural lemmas for Skeleton, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Skeleton.lean

module
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.HopkinsLevitzki
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PretorsionImageClosed
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
abbrev RightFGModule (A : Type*) [Ring A] [IsNoetherianRing Aᵐᵒᵖ] :=
  FGModuleCat Aᵐᵒᵖ
structure IndecomposableSkeleton
    (R : Type u) [Ring R] [IsNoetherianRing R]
    (ι : Type v) where
  obj : ι → FGModuleCat.{w} R
  indecomposable :
    ∀ i, PretorsionImageClosed.IsIndecomposableModule R (obj i)
  finiteLength :
    ∀ i, IsFiniteLength R (obj i)
  eq_of_iso :
    ∀ {i j}, Nonempty (obj i ≅ obj j) → i = j
  complete :
    ∀ X : FGModuleCat.{w} R,
      PretorsionImageClosed.IsIndecomposableModule R X →
        ∃ i, Nonempty (X ≅ obj i)
  decomposes :
    ∀ X : FGModuleCat.{w} R,
      ∃ (n : ℕ) (a : Fin n → ι),
        Nonempty (X ≅ biproduct fun t ↦ obj (a t))
set_option linter.checkUnivs false in
/-- A finite chosen skeleton, with its representative type bundled.
The index and module universes intentionally occur together in the bundled
`IndecomposableSkeleton`. -/
structure FiniteIndecomposableSkeleton
    (R : Type u) [Ring R] [IsNoetherianRing R] where
  ι : Type v
  finite_ι : Finite ι
  skeleton : IndecomposableSkeleton.{u, v, w} R ι
namespace FiniteIndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
instance (M : FiniteIndecomposableSkeleton.{u, v, w} R) :
    Finite M.ι :=
  M.finite_ι
end FiniteIndecomposableSkeleton
namespace IndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
abbrev sum (n : ℕ) (a : Fin n → ι) : FGModuleCat.{w} R :=
  biproduct fun t ↦ σ.obj (a t)
end IndecomposableSkeleton
end PretorsionImageClosed


