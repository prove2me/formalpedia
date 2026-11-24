-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMParameterQuotient
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMParameterQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:40.150806+00:00
-- url     : https://prove2.me/theorems/6c3a5e8c-ca31-4047-9f07-851884364c41
-- title:
--   St CMParameter Quotient
-- statement:
--   Definitions and structural lemmas for St CMParameter Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCMParameterQuotient.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects
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
def CMParameterQuotient.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsCohenMacaulayLocalRing B] (d : ℕ) (x : Fin d → B),
    (∀ i, x i ∈ maximalIdeal B) →
    ringKrullDim (B ⧸ Ideal.span (Set.range x)) + (d : WithBot ℕ∞) = ringKrullDim B →
      IsCohenMacaulayLocalRing (B ⧸ Ideal.span (Set.range x))
end GroundTheory.Heights₂.Heights


