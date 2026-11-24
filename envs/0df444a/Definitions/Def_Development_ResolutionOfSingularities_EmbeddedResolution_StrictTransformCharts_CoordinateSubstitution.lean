-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:58.835746+00:00
-- url     : https://prove2.me/theorems/8e7c4472-9f59-41b7-a60b-5ea1a3c38757
-- title:
--   Coordinate Substitution
-- statement:
--   Definitions and structural lemmas for Coordinate Substitution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateSubstitution.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def coordBlowupSubstMap (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) :
    affineSpaceFin k m ⟶ affineSpaceFin k m :=
  AffineSpace.homOfVector (affineSpaceFinToSpec k m)
    (fun i : ULift.{u} (Fin m) =>
      if i.down ∈ S ∧ i.down ≠ s then
        AffineSpace.coord (Spec (CommRingCat.of k)) i *
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)
      else AffineSpace.coord (Spec (CommRingCat.of k)) i)
end FunctorialResolution.EmbeddedResolution
end


