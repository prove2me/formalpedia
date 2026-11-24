-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAdicCompletionRegular
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAdicCompletionRegular
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:03.563655+00:00
-- url     : https://prove2.me/theorems/a4ed43d8-d3b0-4833-9ac1-d2b3f4eef2e9
-- title:
--   St Adic Completion Regular
-- statement:
--   Definitions and structural lemmas for St Adic Completion Regular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StAdicCompletionRegular.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibresRegular
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
def AdicCompletionRegular.Statement : Prop :=
  ∀ (R : Type) [CommRing R], IsNoetherianRing R → ∀ (M : Ideal R) [M.IsMaximal],
    IsRegularLocalRing (Localization.AtPrime M) → IsRegularLocalRing (AdicCompletion M R)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


