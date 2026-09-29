-- Prove2me | Definitions.Def_Freiman_section14StateData3
-- name    : Freiman_section14StateData3
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:42:36.168778+00:00
-- url     : https://prove2.me/theorems/1c7da98d-86fc-43f7-bf83-4cea7959eee9
-- title:
--   Freiman §14: section14StateData3
-- statement:
--   Exact §14 source model, finite verifier or lossless report data; no theorem or axiom declarations.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14CoreData
import Definitions.Def_Freiman_section14StateData3Part1
import Definitions.Def_Freiman_section14StateData3Part2
import Definitions.Def_Freiman_section14StateData3Part3
import Definitions.Def_Freiman_section14StateData3Part4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def section14DataStates3 : List Section14State :=
  section14DataStates3Part1 ++ section14DataStates3Part2 ++ section14DataStates3Part3 ++ section14DataStates3Part4

end Freiman


