-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl002
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl002
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T15:50:43.759545+00:00
-- url     : https://prove2.me/theorems/202c3828-36b5-4ba4-a625-6ad3ef4e2a50
-- title:
--   Sensitivity record composition: checked_type6_27_assembly_from4672
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_27_assembly_from4672, isolated as one complete proof with its original statement and proof bytes.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition01_Decl001
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check01
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check02
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check03
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check04
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_27_assembly_from4672 : checkCasesFrom tree [5,5,5,5,5,5] 4672=true :=
  checkCasesFrom_step tree [5,5,5,5,5,5] 4672 64 checked_type6_27_chunk4672 (checkCasesFrom_step tree [5,5,5,5,5,5] 4736 64 checked_type6_27_chunk4736 (checkCasesFrom_step tree [5,5,5,5,5,5] 4800 64 checked_type6_27_chunk4800 (checkCasesFrom_step tree [5,5,5,5,5,5] 4864 64 checked_type6_27_chunk4864 (checked_type6_27_assembly_from4928))))


end ThreeBoundEndpoint40Records


