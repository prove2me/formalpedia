-- Prove2me | Definitions.Def_Freiman_section14RecordData2
-- name    : Freiman_section14RecordData2
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:38:39.271681+00:00
-- url     : https://prove2.me/theorems/d018b50e-bfec-41b8-9028-d7253e256d89
-- title:
--   Freiman §14: section14RecordData2
-- statement:
--   Exact §14 source model, finite verifier or lossless report data; no theorem or axiom declarations.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14Model
import Definitions.Def_Freiman_section14RecordData2Part1
import Definitions.Def_Freiman_section14RecordData2Part2
import Definitions.Def_Freiman_section14RecordData2Part3
import Definitions.Def_Freiman_section14RecordData2Part4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def section14DataRecords2 : List Section14Record :=
  section14DataRecords2Part1 ++ section14DataRecords2Part2 ++ section14DataRecords2Part3 ++ section14DataRecords2Part4

end Freiman


