-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl003
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl003
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T15:53:51.687667+00:00
-- url     : https://prove2.me/theorems/97196bf5-be25-4d57-af7b-23527caeda11
-- title:
--   Sensitivity record composition: checked_type6_27_assembly_from4416
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_27_assembly_from4416, isolated as one complete proof with its original statement and proof bytes.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl002
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks058_Check09
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks058_Check10
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks058_Check11
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check00
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_27_assembly_from4416 : checkCasesFrom tree [5,5,5,5,5,5] 4416=true :=
  checkCasesFrom_step tree [5,5,5,5,5,5] 4416 64 checked_type6_27_chunk4416 (checkCasesFrom_step tree [5,5,5,5,5,5] 4480 64 checked_type6_27_chunk4480 (checkCasesFrom_step tree [5,5,5,5,5,5] 4544 64 checked_type6_27_chunk4544 (checkCasesFrom_step tree [5,5,5,5,5,5] 4608 64 checked_type6_27_chunk4608 (checked_type6_27_assembly_from4672))))


end ThreeBoundEndpoint40Records


