-- Prove2me | Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
-- name    : D1Bound5_SmallPairLightData6LeftRows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:08:59.788186+00:00
-- url     : https://prove2.me/theorems/db6793e0-5745-4c7e-ac04-3268cb680f79
-- title:
--   Small Pair Light Data6Left Rows
-- statement:
--   Exact row data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairLightPrepared6.leftRows`.
-- source:
--   D1Bound5/SmallPairLightData6LeftRows.lean, lines 8-667, SHA-256 8ca1557e7060232b8139c4cd9be0222e4cb65acda6714c373db1dda7343bb1e1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_Prove2MeTransfer_rowData_07647d30aaf7d017_part01
import Definitions.Def_D1Bound5_Prove2MeTransfer_rowData_07647d30aaf7d017_part02
import Init

section
namespace D1Bound5.PairLightPrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def leftRows : List (Nat × List Nat) := _root_.List.append _root_.D1Bound5.Prove2MeTransfer.rowData_07647d30aaf7d017_part01 _root_.D1Bound5.Prove2MeTransfer.rowData_07647d30aaf7d017_part02

end D1Bound5.PairLightPrepared6
end


