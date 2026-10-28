-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks063_Check04
-- name    : BS2_b3ba934b_Endpoint40RecordChecks063_Check04
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T14:59:56.250433+00:00
-- url     : https://prove2.me/theorems/f57d11e2-7b8d-4126-b3e8-d850c399646c
-- title:
--   Sensitivity separation: Endpoint40RecordChecks063 certificate 5
-- statement:
--   The unchanged exhaustive-certificate assertion ThreeBoundEndpoint40Records.checked_type6_31_chunk0. Its original statement and complete kernel-decide proof are preserved and published separately to reduce work per compilation job.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks063.lean; original SHA-256 be473fbf748907b12f5977b479be61994a26245bca16188173dfe2b2df4c0721; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks063_Check03
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_31_chunk0 : checkCasesChunk tree [5,5,5,5,7,7] 0 64=true := by decide +kernel

end ThreeBoundEndpoint40Records


