-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl011
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl011
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T16:59:31.434758+00:00
-- url     : https://prove2.me/theorems/cf14956b-7ffc-488a-b404-fe77e528648b
-- title:
--   Sensitivity record composition: checked_type6_27_assembly_from2368
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_27_assembly_from2368, isolated as one complete proof with its original statement and proof bytes.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl010
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks056
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_27_assembly_from2368 : checkCasesFrom tree [5,5,5,5,5,5] 2368=true :=
  checkCasesFrom_step tree [5,5,5,5,5,5] 2368 64 checked_type6_27_chunk2368 (checkCasesFrom_step tree [5,5,5,5,5,5] 2432 64 checked_type6_27_chunk2432 (checkCasesFrom_step tree [5,5,5,5,5,5] 2496 64 checked_type6_27_chunk2496 (checkCasesFrom_step tree [5,5,5,5,5,5] 2560 64 checked_type6_27_chunk2560 (checked_type6_27_assembly_from2624))))


end ThreeBoundEndpoint40Records


