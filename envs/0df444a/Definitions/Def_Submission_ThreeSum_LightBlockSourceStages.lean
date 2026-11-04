-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
-- name    : Submission_ThreeSum_LightBlockSourceStages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:47:25.436762+00:00
-- url     : https://prove2.me/theorems/7a6a57aa-a1eb-42a4-b8fa-2917578aa38b
-- title:
--   Light Block Source Stages
-- statement:
--   Definitions and structural lemmas for Light Block Source Stages, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceStages.lean

import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
import Definitions.Def_Submission_ThreeSum_BlockSourceTableLayout
set_option autoImplicit false
namespace ThreeSum.LightBlockSourceStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightBlockSourceStages


