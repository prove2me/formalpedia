-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_ClosedEmbeddingIntoAffineSpace
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_ClosedEmbeddingIntoAffineSpace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:06.84725+00:00
-- url     : https://prove2.me/theorems/4db38f7d-4b8f-466f-9c6c-455b49e3939c
-- title:
--   Closed Embedding Into Affine Space
-- statement:
--   Definitions and structural lemmas for Closed Embedding Into Affine Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/ClosedEmbeddingIntoAffineSpace.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothCoordinateCodimension
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_EmbeddedResolutionRule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
structure ClosedEmbeddingIntoAffineSpace {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) where
  codimBound : ℕ
  dim : ℕ
  toAffine : G.ambient ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin dim))
  one_le_codimBound : 1 ≤ codimBound
  one_le_dim : 1 ≤ dim
  isClosedImmersion_toAffine : AlgebraicGeometry.IsClosedImmersion toAffine
  toAffine_comp : toAffine ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin dim)) = G.ambientStruct
  locallyConstCodim :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u} (Fin dim))) toAffine codimBound
namespace ClosedEmbeddingIntoAffineSpace
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
  {p : Y ⟶ Spec (CommRingCat.of k)} {G : EmbeddingDatum k Y p}
instance instIsClosedImmersionToAffine (P : ClosedEmbeddingIntoAffineSpace G) :
    AlgebraicGeometry.IsClosedImmersion P.toAffine :=
  P.isClosedImmersion_toAffine
end ClosedEmbeddingIntoAffineSpace
def EmbeddedResolutionRule.IsIndependentOfPresentedEmbedding (R : EmbeddedResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (D D' : EmbeddingDatum k Y p),
    ClosedEmbeddingIntoAffineSpace D → ClosedEmbeddingIntoAffineSpace D' →
    (R k Y p D).Isomorphic (R k Y p D')
end FunctorialResolution.EmbeddedResolution
end


