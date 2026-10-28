-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks058_Check07
-- name    : BS2_b3ba934b_Endpoint40RecordChecks058_Check07
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:12:13.74389+00:00
-- url     : https://prove2.me/theorems/b63fc41b-65de-413f-a314-7ce7106e42f9
-- title:
--   Sensitivity separation: Endpoint40RecordChecks058 certificate 8
-- statement:
--   The unchanged exhaustive-certificate assertion ThreeBoundEndpoint40Records.checked_type6_27_chunk4288. Its original statement and complete kernel-decide proof are preserved and published separately to reduce work per compilation job.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks058.lean; original SHA-256 499fa18ba4b08603af83a80c8353d827c92c075bdee0e6797648ec85b0d437df; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks058_Check06
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_27_chunk4288 : checkCasesChunk tree [5,5,5,5,5,5] 4288 64=true := by decide +kernel

end ThreeBoundEndpoint40Records


