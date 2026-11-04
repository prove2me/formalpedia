-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
-- name    : Submission_ThreeSum_LightLocalCoverCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:11:35.574717+00:00
-- url     : https://prove2.me/theorems/67f84de8-dc39-4ae8-b262-e5d9fa095ff9
-- title:
--   Light Local Cover Cost
-- statement:
--   Definitions and structural lemmas for Light Local Cover Cost, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverCost.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
set_option autoImplicit false
namespace ThreeSum.LightLocalCoverCost
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
set_option maxHeartbeats 1500000
end ThreeSum.LightLocalCoverCost


