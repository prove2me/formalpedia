-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
-- name    : Formalism_PeriodIntegrals_QmRowForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:42:53.168808+00:00
-- url     : https://prove2.me/theorems/97b164f9-c8fd-46da-bc98-57227668f51f
-- title:
--   Qm Row Form
-- statement:
--   Definitions and structural lemmas for Qm Row Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/QmRowForm.lean

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
def QmRowForm : Prop := RowForm
end PI


