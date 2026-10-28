-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check05
-- name    : BS2_b3ba934b_Endpoint40RecordChecks059_Check05
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:07:59.385066+00:00
-- url     : https://prove2.me/theorems/59372f5d-e1bf-41b1-93bb-8240e8b9c030
-- title:
--   Sensitivity separation: Endpoint40RecordChecks059 certificate 6
-- statement:
--   The unchanged exhaustive-certificate assertion ThreeBoundEndpoint40Records.checked_type6_27_chunk4928. Its original statement and complete kernel-decide proof are preserved and published separately to reduce work per compilation job.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks059.lean; original SHA-256 8fc8923cb5f2a3e5c13928b8b8b424483b28231d12d750b62dd39835ae907b4d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check04
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_27_chunk4928 : checkCasesChunk tree [5,5,5,5,5,5] 4928 64=true := by decide +kernel

end ThreeBoundEndpoint40Records


