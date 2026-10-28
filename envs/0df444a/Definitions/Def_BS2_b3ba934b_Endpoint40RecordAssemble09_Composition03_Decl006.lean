-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl006
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl006
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T17:45:07.395432+00:00
-- url     : https://prove2.me/theorems/08df26fc-eb5d-43e8-b186-86ed90e98b77
-- title:
--   Sensitivity record composition: checked_type6_29_assembly_from640
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_29_assembly_from640, isolated as one complete proof with its original statement and proof bytes.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl005
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks061
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_29_assembly_from640 : checkCasesFrom tree [5,5,5,5,5,7] 640=true :=
  checkCasesFrom_step tree [5,5,5,5,5,7] 640 64 checked_type6_29_chunk640 (checkCasesFrom_step tree [5,5,5,5,5,7] 704 64 checked_type6_29_chunk704 (checkCasesFrom_step tree [5,5,5,5,5,7] 768 64 checked_type6_29_chunk768 (checkCasesFrom_step tree [5,5,5,5,5,7] 832 64 checked_type6_29_chunk832 (checked_type6_29_assembly_from896))))


end ThreeBoundEndpoint40Records


