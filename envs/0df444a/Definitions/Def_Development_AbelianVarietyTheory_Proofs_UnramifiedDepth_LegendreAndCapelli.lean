-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:31:05.363938+00:00
-- url     : https://prove2.me/theorems/0d5a6322-90c4-4551-9405-aad84f1352c1
-- title:
--   Legendre And Capelli
-- statement:
--   Definitions and structural lemmas for Legendre And Capelli, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LegendreAndCapelli.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
namespace GlobalTheory.LegendreFacts
open GlobalTheory.LegendreBounds
end GlobalTheory.LegendreFacts


