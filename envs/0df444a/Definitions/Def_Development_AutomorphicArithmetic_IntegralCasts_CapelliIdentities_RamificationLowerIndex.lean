-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RamificationLowerIndex
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RamificationLowerIndex
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:37.400731+00:00
-- url     : https://prove2.me/theorems/911352b4-c4de-43a1-b3c0-f1ad8b4cbc8f
-- title:
--   Ramification Lower Index
-- statement:
--   Definitions and structural lemmas for Ramification Lower Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/RamificationLowerIndex.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace UpperTheory.Reformulated.B.RamificationLowerIndex
open Polynomial IsLocalRing ValuativeRel
open IsDiscreteValuationRing hiding maximalIdeal
end UpperTheory.Reformulated.B.RamificationLowerIndex


