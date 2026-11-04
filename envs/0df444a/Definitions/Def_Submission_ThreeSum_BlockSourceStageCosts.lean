-- Prove2me | Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
-- name    : Submission_ThreeSum_BlockSourceStageCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:38:58.03087+00:00
-- url     : https://prove2.me/theorems/8fbecb87-4bfd-4455-840f-8ced0376e1ce
-- title:
--   Block Source Stage Costs
-- statement:
--   Definitions and structural lemmas for Block Source Stage Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceStageCosts.lean

import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
set_option autoImplicit false
namespace ThreeSum.BlockSourceStageCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing
def work (n : ℕ) : ℕ :=
  bandCount n*scheduleCount n*LightBlockSourceRetainedHost.time
    (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n)
end ThreeSum.BlockSourceStageCosts


