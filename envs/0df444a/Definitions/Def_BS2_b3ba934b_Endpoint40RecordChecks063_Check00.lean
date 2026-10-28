-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks063_Check00
-- name    : BS2_b3ba934b_Endpoint40RecordChecks063_Check00
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T14:54:57.499051+00:00
-- url     : https://prove2.me/theorems/71f2ca8f-784b-46d9-8148-c3baad2791e3
-- title:
--   Sensitivity separation: Endpoint40RecordChecks063 certificate 1
-- statement:
--   The unchanged exhaustive-certificate assertion ThreeBoundEndpoint40Records.checked_type6_29_chunk2048. Its original statement and complete kernel-decide proof are preserved and published separately to reduce work per compilation job.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks063.lean; original SHA-256 be473fbf748907b12f5977b479be61994a26245bca16188173dfe2b2df4c0721; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_29_chunk2048 : checkCasesChunk tree [5,5,5,5,5,7] 2048 64=true := by decide +kernel

end ThreeBoundEndpoint40Records


