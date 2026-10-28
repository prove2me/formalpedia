-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check00
-- name    : BS2_b3ba934b_Endpoint40RecordChecks059_Check00
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T14:55:05.153003+00:00
-- url     : https://prove2.me/theorems/d7617555-5f79-4bc7-bce4-85a31a1b13c1
-- title:
--   Sensitivity separation: Endpoint40RecordChecks059 certificate 1
-- statement:
--   The unchanged exhaustive-certificate assertion ThreeBoundEndpoint40Records.checked_type6_27_chunk4608. Its original statement and complete kernel-decide proof are preserved and published separately to reduce work per compilation job.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks059.lean; original SHA-256 8fc8923cb5f2a3e5c13928b8b8b424483b28231d12d750b62dd39835ae907b4d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_27_chunk4608 : checkCasesChunk tree [5,5,5,5,5,5] 4608 64=true := by decide +kernel

end ThreeBoundEndpoint40Records


