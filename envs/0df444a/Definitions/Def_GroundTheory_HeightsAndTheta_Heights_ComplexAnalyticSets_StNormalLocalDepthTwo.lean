-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocalDepthTwo
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocalDepthTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:55.491393+00:00
-- url     : https://prove2.me/theorems/5b51e57b-8e65-445a-b0aa-c26b86ef51fc
-- title:
--   St Normal Local Depth Two
-- statement:
--   Definitions and structural lemmas for St Normal Local Depth Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalLocalDepthTwo.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
def NormalLocalDepthTwo.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B],
    SerreSAt B 2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


