-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompletionNormalDescent
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompletionNormalDescent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:03.37681+00:00
-- url     : https://prove2.me/theorems/e3a15ac6-3712-4bd6-86cb-c31e0cac58e2
-- title:
--   St Completion Normal Descent
-- statement:
--   Definitions and structural lemmas for St Completion Normal Descent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCompletionNormalDescent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
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
def CompletionNormalDescent.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (J : Ideal R), IsNoetherianRing R → J ≤ (⊥ : Ideal R).jacobson →
    IsDomain (AdicCompletion J R) → IsIntegrallyClosed (AdicCompletion J R) →
      IsDomain R ∧ IsIntegrallyClosed R
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


