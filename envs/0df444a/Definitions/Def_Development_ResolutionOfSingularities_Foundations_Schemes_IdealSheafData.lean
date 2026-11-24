-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
-- name    : Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:05.464646+00:00
-- url     : https://prove2.me/theorems/05638033-23c8-47c8-af30-c0b0d8ea59d6
-- title:
--   Ideal Sheaf Data
-- statement:
--   Definitions and structural lemmas for Ideal Sheaf Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/IdealSheafData.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
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
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}
end AlgebraicGeometry.Scheme.IdealSheafData
namespace FunctorialResolution.Blowup
theorem noetherianSpace_subscheme {X : Scheme.{u}} (I : X.IdealSheafData)
    [TopologicalSpace.NoetherianSpace ↥X] :
    TopologicalSpace.NoetherianSpace ↥I.subscheme :=
  (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding
    I.subschemeι).toIsEmbedding.toIsInducing.noetherianSpace
instance instNoetherianSpaceSubscheme {X : Scheme.{u}} (I : X.IdealSheafData)
    [TopologicalSpace.NoetherianSpace ↥X] :
    TopologicalSpace.NoetherianSpace ↥I.subscheme :=
  noetherianSpace_subscheme I
end FunctorialResolution.Blowup
namespace AlgebraicGeometry.Scheme.IdealSheafData
end AlgebraicGeometry.Scheme.IdealSheafData


