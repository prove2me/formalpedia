-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
-- name    : Submission_ThreeSum_LightLocalCoverResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:15:37.47676+00:00
-- url     : https://prove2.me/theorems/5d6f60a6-62b6-4736-b417-0cddcef582a1
-- title:
--   Light Local Cover Resources
-- statement:
--   Definitions and structural lemmas for Light Local Cover Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverResources.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
set_option autoImplicit false
namespace ThreeSum.LightLocalCoverResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude
set_option maxHeartbeats 1800000
def envelope (h : ℕ) : ℕ := 2^(4000000*(h+1)^2)
end ThreeSum.LightLocalCoverResources


