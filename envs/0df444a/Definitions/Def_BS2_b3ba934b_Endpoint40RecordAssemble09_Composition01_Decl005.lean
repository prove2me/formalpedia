-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl005
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl005
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T16:11:13.089869+00:00
-- url     : https://prove2.me/theorems/84547753-0f1f-4195-8cc1-42f356672cfe
-- title:
--   Sensitivity record composition: checked_type6_27_assembly_from3904
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_27_assembly_from3904, isolated as one complete proof with its original statement and proof bytes.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl004
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks058_Check01
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks058_Check02
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks058_Check03
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks058_Check04
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_27_assembly_from3904 : checkCasesFrom tree [5,5,5,5,5,5] 3904=true :=
  checkCasesFrom_step tree [5,5,5,5,5,5] 3904 64 checked_type6_27_chunk3904 (checkCasesFrom_step tree [5,5,5,5,5,5] 3968 64 checked_type6_27_chunk3968 (checkCasesFrom_step tree [5,5,5,5,5,5] 4032 64 checked_type6_27_chunk4032 (checkCasesFrom_step tree [5,5,5,5,5,5] 4096 64 checked_type6_27_chunk4096 (checked_type6_27_assembly_from4160))))


end ThreeBoundEndpoint40Records


