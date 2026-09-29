-- Prove2me | Definitions.Def_Freiman_section14WitnessData
-- name    : Freiman_section14WitnessData
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:43:21.800578+00:00
-- url     : https://prove2.me/theorems/9387d99c-562d-4be0-ba6d-38b372365e32
-- title:
--   Freiman §14: section14WitnessData
-- statement:
--   Exact §14 source model, finite verifier or lossless report data; no theorem or axiom declarations.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14Model
import Definitions.Def_Freiman_section14WitnessDataPart1
import Definitions.Def_Freiman_section14WitnessDataPart2
import Definitions.Def_Freiman_section14WitnessDataPart3
import Definitions.Def_Freiman_section14WitnessDataPart4
import Definitions.Def_Freiman_section14WitnessDataPart5
import Definitions.Def_Freiman_section14WitnessDataPart6
import Definitions.Def_Freiman_section14WitnessDataPart7
import Definitions.Def_Freiman_section14WitnessDataPart8

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def section14DataProofs : List Section14Proof :=
  section14DataProofsPart1 ++ section14DataProofsPart2 ++ section14DataProofsPart3

def section14DataWitnesses : List Section14Witness :=
  section14DataWitnessesPart1 ++ section14DataWitnessesPart2 ++ section14DataWitnessesPart3

def section14DataAssignments : List Section14Assignment :=
  section14DataAssignmentsPart1 ++ section14DataAssignmentsPart2

end Freiman


