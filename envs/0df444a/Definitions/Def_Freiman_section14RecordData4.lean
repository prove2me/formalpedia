-- Prove2me | Definitions.Def_Freiman_section14RecordData4
-- name    : Freiman_section14RecordData4
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:39:47.742557+00:00
-- url     : https://prove2.me/theorems/b40315f3-0069-4303-ace3-bf91eaeba9c1
-- title:
--   Freiman §14: section14RecordData4
-- statement:
--   Exact §14 source model, finite verifier or lossless report data; no theorem or axiom declarations.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14Model
import Definitions.Def_Freiman_section14RecordData4Part1
import Definitions.Def_Freiman_section14RecordData4Part2
import Definitions.Def_Freiman_section14RecordData4Part3
import Definitions.Def_Freiman_section14RecordData4Part4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def section14DataRecords4 : List Section14Record :=
  section14DataRecords4Part1 ++ section14DataRecords4Part2 ++ section14DataRecords4Part3 ++ section14DataRecords4Part4

end Freiman


