-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_QmSkip
-- name    : Formalism_PeriodIntegrals_QmSkip
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:43:24.11072+00:00
-- url     : https://prove2.me/theorems/de03a19c-9d7e-4319-b74c-631e64698c7b
-- title:
--   Qm Skip
-- statement:
--   Definitions and structural lemmas for Qm Skip, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/QmSkip.lean

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
def QmSkip : Prop := SkipSucc ∧ SkipSucc2
end PI


