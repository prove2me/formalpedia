-- Prove2me | Definitions.Def_Freiman_section14RecordData3
-- name    : Freiman_section14RecordData3
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:39:43.973257+00:00
-- url     : https://prove2.me/theorems/218cac02-a003-4bdb-ae11-611772cf3ba2
-- title:
--   Freiman §14: section14RecordData3
-- statement:
--   Exact §14 source model, finite verifier or lossless report data; no theorem or axiom declarations.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14Model
import Definitions.Def_Freiman_section14RecordData3Part1
import Definitions.Def_Freiman_section14RecordData3Part2
import Definitions.Def_Freiman_section14RecordData3Part3
import Definitions.Def_Freiman_section14RecordData3Part4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def section14DataRecords3 : List Section14Record :=
  section14DataRecords3Part1 ++ section14DataRecords3Part2 ++ section14DataRecords3Part3 ++ section14DataRecords3Part4

end Freiman


