-- Prove2me | Definitions.Def_Freiman_section14RecordData1
-- name    : Freiman_section14RecordData1
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:38:27.127728+00:00
-- url     : https://prove2.me/theorems/324813ed-0f23-47cd-b8eb-525e30fe71a7
-- title:
--   Freiman §14: section14RecordData1
-- statement:
--   Exact §14 source model, finite verifier or lossless report data; no theorem or axiom declarations.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14Model
import Definitions.Def_Freiman_section14RecordData1Part1
import Definitions.Def_Freiman_section14RecordData1Part2
import Definitions.Def_Freiman_section14RecordData1Part3
import Definitions.Def_Freiman_section14RecordData1Part4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def section14DataRecords1 : List Section14Record :=
  section14DataRecords1Part1 ++ section14DataRecords1Part2 ++ section14DataRecords1Part3 ++ section14DataRecords1Part4

end Freiman


