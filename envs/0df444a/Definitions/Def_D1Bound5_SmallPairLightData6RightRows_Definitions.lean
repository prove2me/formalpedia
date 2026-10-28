-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
-- name    : D1Bound5_SmallPairLightData6RightRows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:37:13.641397+00:00
-- url     : https://prove2.me/theorems/0bced410-f441-4bcb-84ac-d001af7f1add
-- title:
--   Small Pair Light Data6Right Rows
-- statement:
--   Exact row data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared6.rightRows`.
-- source:
--   D1Bound5/SmallPairLightData6RightRows.lean, lines 8-666, SHA-256 86de0c267d3658ad48740d20e61144f77cf06068c80285916014d12a0bb28abd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_rowData_82d20c9bf548cd81_part01
import Definitions.Def_D1Bound5_Prove2MeTransfer_rowData_82d20c9bf548cd81_part02
import Init

section
namespace D1Bound5.PairLightPrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def rightRows : List (Nat × List Nat) := _root_.List.append _root_.D1Bound5.Prove2MeTransfer.rowData_82d20c9bf548cd81_part01 _root_.D1Bound5.Prove2MeTransfer.rowData_82d20c9bf548cd81_part02

end D1Bound5.PairLightPrepared6
end


