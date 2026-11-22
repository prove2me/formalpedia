-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_QmMove
-- name    : Formalism_PeriodIntegrals_QmMove
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:50:13.998913+00:00
-- url     : https://prove2.me/theorems/153ae193-31bb-4a15-b347-34bfdb1cf472
-- title:
--   Qm Move
-- statement:
--   Definitions and structural lemmas for Qm Move, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/QmMove.lean

import Definitions.Def_Formalism_PeriodIntegrals_QmDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
def QmMove : Prop := MoveVec ∧ MoveCov
end PI


