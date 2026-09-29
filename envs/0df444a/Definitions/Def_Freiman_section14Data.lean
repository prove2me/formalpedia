-- Prove2me | Definitions.Def_Freiman_section14Data
-- name    : Freiman_section14Data
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:45:32.060207+00:00
-- url     : https://prove2.me/theorems/915593ca-0fe2-43d2-918b-dba80c812d84
-- title:
--   Freiman §14: section14Data
-- statement:
--   Exact §14 source model, finite verifier or lossless report data; no theorem or axiom declarations.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14CoreData
import Definitions.Def_Freiman_section14GoalData
import Definitions.Def_Freiman_section14WitnessData
import Definitions.Def_Freiman_section14RecordData1
import Definitions.Def_Freiman_section14RecordData2
import Definitions.Def_Freiman_section14RecordData3
import Definitions.Def_Freiman_section14RecordData4
import Definitions.Def_Freiman_section14StateData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def section14Catalog : Section14Catalog :=
  ⟨section14DataTails,section14DataThresholds,section14DataEndpoints,section14DataParents,
   section14DataCases,section14DataGoals,section14DataProofs,section14DataWitnesses,
   section14DataAssignments,section14DataRecords1++section14DataRecords2++section14DataRecords3++section14DataRecords4,
   section14DataStates⟩

end Freiman


