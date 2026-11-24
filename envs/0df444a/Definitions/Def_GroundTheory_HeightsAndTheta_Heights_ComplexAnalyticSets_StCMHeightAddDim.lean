-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightAddDim
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightAddDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:27.192164+00:00
-- url     : https://prove2.me/theorems/892ef8fc-a9a7-4aa0-bf52-af10a6029296
-- title:
--   St CMHeight Add Dim
-- statement:
--   Definitions and structural lemmas for St CMHeight Add Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCMHeightAddDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects
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
universe u
def CMHeightAddDim.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (J : Ideal B), J ≠ ⊤ →
    (J.height : WithBot ℕ∞) + ringKrullDim (B ⧸ J) = ringKrullDim B
end GroundTheory.Heights₂.Heights


