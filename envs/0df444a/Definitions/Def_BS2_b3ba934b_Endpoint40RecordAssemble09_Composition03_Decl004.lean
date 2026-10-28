-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl004
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl004
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T17:28:02.085642+00:00
-- url     : https://prove2.me/theorems/d5e26cb8-c81d-4525-84bf-0ce3526871bb
-- title:
--   Sensitivity record composition: checked_type6_29_assembly_from1152
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_29_assembly_from1152, isolated as one complete proof with its original statement and proof bytes.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl003
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks061
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks062_Check00
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks062_Check01
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_29_assembly_from1152 : checkCasesFrom tree [5,5,5,5,5,7] 1152=true :=
  checkCasesFrom_step tree [5,5,5,5,5,7] 1152 64 checked_type6_29_chunk1152 (checkCasesFrom_step tree [5,5,5,5,5,7] 1216 64 checked_type6_29_chunk1216 (checkCasesFrom_step tree [5,5,5,5,5,7] 1280 64 checked_type6_29_chunk1280 (checkCasesFrom_step tree [5,5,5,5,5,7] 1344 64 checked_type6_29_chunk1344 (checked_type6_29_assembly_from1408))))


end ThreeBoundEndpoint40Records


