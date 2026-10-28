-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks063_Check09
-- name    : BS2_b3ba934b_Endpoint40RecordChecks063_Check09
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:08:58.476548+00:00
-- url     : https://prove2.me/theorems/821e200c-3bf0-4f58-92a5-9e15a1a73691
-- title:
--   Sensitivity separation: Endpoint40RecordChecks063 certificate 10
-- statement:
--   The unchanged exhaustive-certificate assertion ThreeBoundEndpoint40Records.checked_type6_31_chunk320. Its original statement and complete kernel-decide proof are preserved and published separately to reduce work per compilation job.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks063.lean; original SHA-256 be473fbf748907b12f5977b479be61994a26245bca16188173dfe2b2df4c0721; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks063_Check08
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_31_chunk320 : checkCasesChunk tree [5,5,5,5,7,7] 320 64=true := by decide +kernel

end ThreeBoundEndpoint40Records


