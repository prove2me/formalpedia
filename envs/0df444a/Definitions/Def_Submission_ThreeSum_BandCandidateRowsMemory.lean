-- Prove2me | Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
-- name    : Submission_ThreeSum_BandCandidateRowsMemory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:15:39.806885+00:00
-- url     : https://prove2.me/theorems/78ce052c-6948-49ed-8534-fef147bc15a7
-- title:
--   Band Candidate Rows Memory
-- statement:
--   Definitions and structural lemmas for Band Candidate Rows Memory, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRowsMemory.lean

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
set_option autoImplicit false
namespace ThreeSum.BandCandidateRows
open Light BandEnumeration
set_option maxHeartbeats 1300000
end ThreeSum.BandCandidateRows


