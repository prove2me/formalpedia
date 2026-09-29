-- Prove2me | Definitions.Def_Freiman_section14StateData2
-- name    : Freiman_section14StateData2
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:41:31.18955+00:00
-- url     : https://prove2.me/theorems/0b76723b-2ffc-4afb-a142-30eb499d63c6
-- title:
--   Freiman §14: section14StateData2
-- statement:
--   Exact §14 source model, finite verifier or lossless report data; no theorem or axiom declarations.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14CoreData
import Definitions.Def_Freiman_section14StateData2Part1
import Definitions.Def_Freiman_section14StateData2Part2
import Definitions.Def_Freiman_section14StateData2Part3
import Definitions.Def_Freiman_section14StateData2Part4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def section14DataStates2 : List Section14State :=
  section14DataStates2Part1 ++ section14DataStates2Part2 ++ section14DataStates2Part3 ++ section14DataStates2Part4

end Freiman


