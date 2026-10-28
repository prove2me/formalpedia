-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl007
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl007
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T16:38:14.217774+00:00
-- url     : https://prove2.me/theorems/f5f8f374-cc39-4085-b7f1-f9368cb33fd3
-- title:
--   Sensitivity record composition: checked_type6_27_assembly_from3392
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_27_assembly_from3392, isolated as one complete proof with its original statement and proof bytes.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl006
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks057
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_27_assembly_from3392 : checkCasesFrom tree [5,5,5,5,5,5] 3392=true :=
  checkCasesFrom_step tree [5,5,5,5,5,5] 3392 64 checked_type6_27_chunk3392 (checkCasesFrom_step tree [5,5,5,5,5,5] 3456 64 checked_type6_27_chunk3456 (checkCasesFrom_step tree [5,5,5,5,5,5] 3520 64 checked_type6_27_chunk3520 (checkCasesFrom_step tree [5,5,5,5,5,5] 3584 64 checked_type6_27_chunk3584 (checked_type6_27_assembly_from3648))))


end ThreeBoundEndpoint40Records


