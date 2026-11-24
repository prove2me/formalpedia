-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothCoordinateCodimension
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothCoordinateCodimension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:41.330304+00:00
-- url     : https://prove2.me/theorems/2293feae-8df4-4240-85cb-58b38f4b8fdf
-- title:
--   Smooth Coordinate Codimension
-- statement:
--   Definitions and structural lemmas for Smooth Coordinate Codimension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothCoordinateCodimension.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
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
def HasSmoothCoordCodim {X Y : Scheme.{u}} {k : Type u} [Field k]
    (s : Y ⟶ Spec (CommRingCat.of k)) (t : X ⟶ Y) (c : ℕ) : Prop :=
  ∀ x : X, ∃ (U : Y.Opens) (_ : t.base x ∈ U)
    (q : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))),
    AlgebraicGeometry.Smooth q ∧
      q ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) = U.ι ≫ s ∧
      restrictIdeal t.ker U = (coordSubspaceIdeal k c Finset.univ).comap q
end FunctorialResolution.EmbeddedResolution
end


