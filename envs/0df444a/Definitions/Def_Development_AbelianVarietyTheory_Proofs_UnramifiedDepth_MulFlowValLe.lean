-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulFlowValLe
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulFlowValLe
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:14:49.40226+00:00
-- url     : https://prove2.me/theorems/02aab0b1-c865-4479-a653-e1a8e10ade80
-- title:
--   Mul Flow Val Le
-- statement:
--   Definitions and structural lemmas for Mul Flow Val Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MulFlowValLe.lean

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
namespace GlobalTheory.FlowScaling
variable {l d : ℕ} [NeZero d]
end GlobalTheory.FlowScaling


