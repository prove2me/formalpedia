-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check03
-- name    : BS2_b3ba934b_Endpoint40RecordChecks059_Check03
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:02:07.09799+00:00
-- url     : https://prove2.me/theorems/9897a2f8-ba66-4cf9-a6dc-ab71e8493e19
-- title:
--   Sensitivity separation: Endpoint40RecordChecks059 certificate 4
-- statement:
--   The unchanged exhaustive-certificate assertion ThreeBoundEndpoint40Records.checked_type6_27_chunk4800. Its original statement and complete kernel-decide proof are preserved and published separately to reduce work per compilation job.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks059.lean; original SHA-256 8fc8923cb5f2a3e5c13928b8b8b424483b28231d12d750b62dd39835ae907b4d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check02
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_27_chunk4800 : checkCasesChunk tree [5,5,5,5,5,5] 4800 64=true := by decide +kernel

end ThreeBoundEndpoint40Records


