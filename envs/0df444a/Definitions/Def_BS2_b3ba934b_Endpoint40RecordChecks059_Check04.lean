-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check04
-- name    : BS2_b3ba934b_Endpoint40RecordChecks059_Check04
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:03:41.682255+00:00
-- url     : https://prove2.me/theorems/ca65de3c-7d51-425e-af15-842b226fdc1c
-- title:
--   Sensitivity separation: Endpoint40RecordChecks059 certificate 5
-- statement:
--   The unchanged exhaustive-certificate assertion ThreeBoundEndpoint40Records.checked_type6_27_chunk4864. Its original statement and complete kernel-decide proof are preserved and published separately to reduce work per compilation job.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks059.lean; original SHA-256 8fc8923cb5f2a3e5c13928b8b8b424483b28231d12d750b62dd39835ae907b4d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check03
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_27_chunk4864 : checkCasesChunk tree [5,5,5,5,5,5] 4864 64=true := by decide +kernel

end ThreeBoundEndpoint40Records


