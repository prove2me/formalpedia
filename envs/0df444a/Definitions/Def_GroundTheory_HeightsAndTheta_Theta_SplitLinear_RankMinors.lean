-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_SplitLinear_RankMinors
-- name    : GroundTheory_HeightsAndTheta_Theta_SplitLinear_RankMinors
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T11:27:07.75617+00:00
-- url     : https://prove2.me/theorems/c828b756-ed4c-448c-8fdd-0959e9e6349e
-- title:
--   Rank Minors
-- statement:
--   Definitions and structural lemmas for Rank Minors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/SplitLinear/RankMinors.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRowsLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Theta
namespace SplitLinear
open Matrix Module
universe u
variable {K : Type*} [Field K]
end SplitLinear
end GroundTheory.Heights₂.Theta


