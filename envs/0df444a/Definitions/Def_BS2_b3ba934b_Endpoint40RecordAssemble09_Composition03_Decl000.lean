-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl000
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl000
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T17:05:10.76249+00:00
-- url     : https://prove2.me/theorems/14d53977-53bb-4bd4-a3a7-c036fe3033a1
-- title:
--   Sensitivity record composition: checked_type6_29_assembly_end
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_29_assembly_end, isolated as one complete proof with its original statement and proof bytes.
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

theorem checked_type6_29_assembly_end : checkCasesFrom tree [5,5,5,5,5,7] 2144=true :=
  checkCasesFrom_end tree [5,5,5,5,5,7] 2144 (by decide +kernel)


end ThreeBoundEndpoint40Records


