-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition02_Decl000
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition02_Decl000
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T16:04:17.831435+00:00
-- url     : https://prove2.me/theorems/f48d62be-a975-4fa8-a89f-c12cc6fa5a39
-- title:
--   Sensitivity record composition: checked_type6_28_assembly_end
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_28_assembly_end, isolated as one complete proof with its original statement and proof bytes.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_28_assembly_end : checkCasesFrom tree [5,5,5,5,5,6] 424=true :=
  checkCasesFrom_end tree [5,5,5,5,5,6] 424 (by decide +kernel)


end ThreeBoundEndpoint40Records


