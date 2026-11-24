-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_OfHookCharacterSumIdentity
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_OfHookCharacterSumIdentity
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T18:31:59.787959+00:00
-- url     : https://prove2.me/theorems/e2746689-a283-49c6-a340-9602a7e86181
-- title:
--   Of Hook Character Sum Identity
-- statement:
--   Definitions and structural lemmas for Of Hook Character Sum Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/OfHookCharacterSumIdentity.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms.HookCharacterShiftIdentity
open Finset
def HookCharacterSumIdentitySmall.Statement : Prop :=
  ∀ r a : ℕ, 1 ≤ r → r ≤ a →
    (a : ℚ) * numStandardTable (fun i : Fin r => a + if (i : ℕ) = 0 then 1 else 0) =
      ∑ k ∈ Finset.Icc 2 (r + a), ∑ l ∈ Finset.range (min r k),
        (-1 : ℚ) ^ l * symmetricGroupCharacter (fun i => a + hookShape r k l i)
          ((k - 1) :: List.replicate (r * a + 1) 1)
end GroundTheory.Heights₂.Heights.RestTerms.HookCharacterShiftIdentity


