-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl008
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl008
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T16:42:44.131822+00:00
-- url     : https://prove2.me/theorems/eb3678f4-7952-459d-9ac3-3c996354e297
-- title:
--   Sensitivity record composition: checked_type6_27_assembly_from3136
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_27_assembly_from3136, isolated as one complete proof with its original statement and proof bytes.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl007
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks057
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_27_assembly_from3136 : checkCasesFrom tree [5,5,5,5,5,5] 3136=true :=
  checkCasesFrom_step tree [5,5,5,5,5,5] 3136 64 checked_type6_27_chunk3136 (checkCasesFrom_step tree [5,5,5,5,5,5] 3200 64 checked_type6_27_chunk3200 (checkCasesFrom_step tree [5,5,5,5,5,5] 3264 64 checked_type6_27_chunk3264 (checkCasesFrom_step tree [5,5,5,5,5,5] 3328 64 checked_type6_27_chunk3328 (checked_type6_27_assembly_from3392))))


end ThreeBoundEndpoint40Records


