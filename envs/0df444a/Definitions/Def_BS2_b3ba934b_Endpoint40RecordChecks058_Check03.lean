-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks058_Check03
-- name    : BS2_b3ba934b_Endpoint40RecordChecks058_Check03
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:00:51.521193+00:00
-- url     : https://prove2.me/theorems/0a1c2a45-7a58-40e9-927f-fdc209883186
-- title:
--   Sensitivity separation: Endpoint40RecordChecks058 certificate 4
-- statement:
--   The unchanged exhaustive-certificate assertion ThreeBoundEndpoint40Records.checked_type6_27_chunk4032. Its original statement and complete kernel-decide proof are preserved and published separately to reduce work per compilation job.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks058.lean; original SHA-256 499fa18ba4b08603af83a80c8353d827c92c075bdee0e6797648ec85b0d437df; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks058_Check02
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_27_chunk4032 : checkCasesChunk tree [5,5,5,5,5,5] 4032 64=true := by decide +kernel

end ThreeBoundEndpoint40Records


