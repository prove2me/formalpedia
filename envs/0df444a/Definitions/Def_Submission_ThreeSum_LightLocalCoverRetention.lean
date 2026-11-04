-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverRetention
-- name    : Submission_ThreeSum_LightLocalCoverRetention
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:23:23.521772+00:00
-- url     : https://prove2.me/theorems/940815c2-3db8-4d20-b505-6f9da11905ef
-- title:
--   Light Local Cover Retention
-- statement:
--   Definitions and structural lemmas for Light Local Cover Retention, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverRetention.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
set_option autoImplicit false
namespace ThreeSum.LightLocalCoverRetention
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata
set_option maxHeartbeats 1000000
end ThreeSum.LightLocalCoverRetention


