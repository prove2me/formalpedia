-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMQuotientUnmixed
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMQuotientUnmixed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:27.159703+00:00
-- url     : https://prove2.me/theorems/c1bd0c11-3782-436a-bd77-03be083bda78
-- title:
--   St CMQuotient Unmixed
-- statement:
--   Definitions and structural lemmas for St CMQuotient Unmixed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCMQuotientUnmixed.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCMUnmixed
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
open MvPolynomial IsLocalRing
def CMQuotientUnmixed.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsCohenMacaulayLocalRing B] (d : ℕ) (x : Fin d → B),
    (∀ i, x i ∈ maximalIdeal B) →
    ringKrullDim (B ⧸ Ideal.span (Set.range x)) + (d : WithBot ℕ∞) = ringKrullDim B →
      ∀ p ∈ associatedPrimes B (B ⧸ Ideal.span (Set.range x)),
        p ∈ (Ideal.span (Set.range x)).minimalPrimes ∧
          ringKrullDim (B ⧸ p) = ringKrullDim (B ⧸ Ideal.span (Set.range x))
end GroundTheory.Heights₂.Heights


