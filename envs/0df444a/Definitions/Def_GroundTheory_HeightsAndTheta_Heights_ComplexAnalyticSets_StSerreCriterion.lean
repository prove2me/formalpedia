-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreCriterion
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreCriterion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:51.758191+00:00
-- url     : https://prove2.me/theorems/ad58ae91-e0a9-40f8-9c1f-443afb951888
-- title:
--   St Serre Criterion
-- statement:
--   Definitions and structural lemmas for St Serre Criterion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSerreCriterion.lean

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
def SerreCriterion.Statement : Prop :=
  ∀ (A : Type) [CommRing A], IsNoetherianRing A → (NormalRing A ↔ SerreR A 1 ∧ SerreS A 2)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


