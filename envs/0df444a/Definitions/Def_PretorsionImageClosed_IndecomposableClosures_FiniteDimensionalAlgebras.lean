-- Prove2me | Definitions.Def_PretorsionImageClosed_IndecomposableClosures_FiniteDimensionalAlgebras
-- name    : PretorsionImageClosed_IndecomposableClosures_FiniteDimensionalAlgebras
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T07:00:43.563265+00:00
-- url     : https://prove2.me/theorems/af1ed931-b9bd-56bd-bf4f-687bc84bc37d
-- title:
--   Finite Dimensional Algebras
-- statement:
--   Definitions and structural lemmas for Finite Dimensional Algebras, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/FiniteDimensionalAlgebras.lean

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Decomposition
public import Theorems.Thm_PretorsionImageClosed_isArtinianRing_mop

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace PretorsionImageClosed
universe u
theorem isFiniteLength_mod (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ] :
    haveI := Statement.isNoetherianRing_mop k Λ
    ∀ X : FGModuleCat.{u} Λᵐᵒᵖ, IsFiniteLength Λᵐᵒᵖ X := by
  haveI := Statement.isNoetherianRing_mop k Λ
  haveI := isArtinianRing_mop k Λ
  intro X
  exact isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
def modSkeleton (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ] :
    haveI := Statement.isNoetherianRing_mop k Λ
    IndecomposableSkeleton.{u, u + 1, u} Λᵐᵒᵖ
      (FiniteLengthDecomposition.CanonicalIndecomposableIndex.{u, u} Λᵐᵒᵖ) :=
  haveI := Statement.isNoetherianRing_mop k Λ
  FiniteLengthDecomposition.canonicalIndecomposableSkeleton (isFiniteLength_mod k Λ)
end PretorsionImageClosed


