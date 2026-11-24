-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:42.048016+00:00
-- url     : https://prove2.me/theorems/e358d6b9-4c58-4219-81c0-edc6193f290a
-- title:
--   St CMRegular Element
-- statement:
--   Definitions and structural lemmas for St CMRegular Element, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCMRegularElement.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
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
open IsLocalRing
universe u
def CMRegularElement.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (y : B), y ∈ maximalIdeal B →
    (∀ p ∈ minimalPrimes B, y ∉ p) →
      y ∈ nonZeroDivisors B ∧ IsCohenMacaulayLocalRing (B ⧸ Ideal.span {y})
end GroundTheory.Heights₂.Heights


