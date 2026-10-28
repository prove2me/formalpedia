-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl001
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl001
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T15:50:04.449206+00:00
-- url     : https://prove2.me/theorems/5bbafe92-67d8-4bb9-b6a1-90ce96b8b5e5
-- title:
--   Sensitivity record composition: checked_type6_27_assembly_from4928
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_27_assembly_from4928, isolated as one complete proof with its original statement and proof bytes.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl000
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check05
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check06
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check07
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check08
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_27_assembly_from4928 : checkCasesFrom tree [5,5,5,5,5,5] 4928=true :=
  checkCasesFrom_step tree [5,5,5,5,5,5] 4928 64 checked_type6_27_chunk4928 (checkCasesFrom_step tree [5,5,5,5,5,5] 4992 64 checked_type6_27_chunk4992 (checkCasesFrom_step tree [5,5,5,5,5,5] 5056 64 checked_type6_27_chunk5056 (checkCasesFrom_step tree [5,5,5,5,5,5] 5120 64 checked_type6_27_chunk5120 (checked_type6_27_assembly_end))))


end ThreeBoundEndpoint40Records


