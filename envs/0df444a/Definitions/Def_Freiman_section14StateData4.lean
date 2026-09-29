-- Prove2me | Definitions.Def_Freiman_section14StateData4
-- name    : Freiman_section14StateData4
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:42:27.498816+00:00
-- url     : https://prove2.me/theorems/de70d3e8-f86b-4be4-a567-adc4262c75f0
-- title:
--   Freiman §14: section14StateData4
-- statement:
--   Exact §14 source model, finite verifier or lossless report data; no theorem or axiom declarations.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14CoreData
import Definitions.Def_Freiman_section14StateData4Part1
import Definitions.Def_Freiman_section14StateData4Part2
import Definitions.Def_Freiman_section14StateData4Part3
import Definitions.Def_Freiman_section14StateData4Part4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def section14DataStates4 : List Section14State :=
  section14DataStates4Part1 ++ section14DataStates4Part2 ++ section14DataStates4Part3 ++ section14DataStates4Part4

end Freiman


