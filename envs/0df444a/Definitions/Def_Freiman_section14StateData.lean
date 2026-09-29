-- Prove2me | Definitions.Def_Freiman_section14StateData
-- name    : Freiman_section14StateData
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:43:40.494993+00:00
-- url     : https://prove2.me/theorems/bd1ef00f-4ffa-4718-80df-a7736301d341
-- title:
--   Freiman §14: section14StateData
-- statement:
--   Exact §14 source model, finite verifier or lossless report data; no theorem or axiom declarations.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14StateData1
import Definitions.Def_Freiman_section14StateData2
import Definitions.Def_Freiman_section14StateData3
import Definitions.Def_Freiman_section14StateData4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def section14DataStates : List Section14State :=
  section14DataStates1++section14DataStates2++section14DataStates3++section14DataStates4

end Freiman


