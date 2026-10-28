-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl003
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl003
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T17:27:26.856537+00:00
-- url     : https://prove2.me/theorems/f2758992-3049-4f42-a33f-1734bae4c217
-- title:
--   Sensitivity record composition: checked_type6_29_assembly_from1408
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_29_assembly_from1408, isolated as one complete proof with its original statement and proof bytes.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl002
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks062_Check02
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks062_Check03
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks062_Check04
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks062_Check05
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_29_assembly_from1408 : checkCasesFrom tree [5,5,5,5,5,7] 1408=true :=
  checkCasesFrom_step tree [5,5,5,5,5,7] 1408 64 checked_type6_29_chunk1408 (checkCasesFrom_step tree [5,5,5,5,5,7] 1472 64 checked_type6_29_chunk1472 (checkCasesFrom_step tree [5,5,5,5,5,7] 1536 64 checked_type6_29_chunk1536 (checkCasesFrom_step tree [5,5,5,5,5,7] 1600 64 checked_type6_29_chunk1600 (checked_type6_29_assembly_from1664))))


end ThreeBoundEndpoint40Records


