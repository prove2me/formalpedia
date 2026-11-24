-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AuslanderBuchsbaumDepthBound
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AuslanderBuchsbaumDepthBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:11.250923+00:00
-- url     : https://prove2.me/theorems/57483c7a-d8f2-4b00-b4ba-01143a77398d
-- title:
--   Auslander Buchsbaum Depth Bound
-- statement:
--   Definitions and structural lemmas for Auslander Buchsbaum Depth Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/AuslanderBuchsbaumDepthBound.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open IsLocalRing CategoryTheory RingTheory.Sequence Ideal
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]
end GroundTheory.Heights₂.Heights


