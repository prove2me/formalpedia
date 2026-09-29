-- Prove2me | Definitions.Def_Freiman_section14StateData1
-- name    : Freiman_section14StateData1
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:41:20.392927+00:00
-- url     : https://prove2.me/theorems/e208b8e0-918e-40fa-b8a0-e14d7c86241a
-- title:
--   Freiman §14: section14StateData1
-- statement:
--   Exact §14 source model, finite verifier or lossless report data; no theorem or axiom declarations.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14CoreData
import Definitions.Def_Freiman_section14StateData1Part1
import Definitions.Def_Freiman_section14StateData1Part2
import Definitions.Def_Freiman_section14StateData1Part3
import Definitions.Def_Freiman_section14StateData1Part4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def section14DataStates1 : List Section14State :=
  section14DataStates1Part1 ++ section14DataStates1Part2 ++ section14DataStates1Part3 ++ section14DataStates1Part4

end Freiman


