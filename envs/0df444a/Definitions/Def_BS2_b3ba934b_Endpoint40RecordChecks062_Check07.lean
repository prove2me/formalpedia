-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks062_Check07
-- name    : BS2_b3ba934b_Endpoint40RecordChecks062_Check07
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:04:56.433408+00:00
-- url     : https://prove2.me/theorems/3a144a67-cefd-42ab-bf1e-61cbff5eae3e
-- title:
--   Sensitivity separation: Endpoint40RecordChecks062 certificate 8
-- statement:
--   The unchanged exhaustive-certificate assertion ThreeBoundEndpoint40Records.checked_type6_29_chunk1728. Its original statement and complete kernel-decide proof are preserved and published separately to reduce work per compilation job.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks062.lean; original SHA-256 41d174b0041abc637597ec1868d67eda8a4f986f9f3bfe4311d36bc491e269b4; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks062_Check06
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_29_chunk1728 : checkCasesChunk tree [5,5,5,5,5,7] 1728 64=true := by decide +kernel

end ThreeBoundEndpoint40Records


