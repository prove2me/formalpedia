-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition02_Decl002
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition02_Decl002
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T16:26:09.319536+00:00
-- url     : https://prove2.me/theorems/7de15a3c-e204-4a55-920d-cc2aa8dd42f9
-- title:
--   Sensitivity record composition: checked_type6_28_assembly_from0
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_28_assembly_from0, isolated as one complete proof with its original statement and proof bytes.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition02_Decl001
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check09
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check10
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks059_Check11
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_28_assembly_from0 : checkCasesFrom tree [5,5,5,5,5,6] 0=true :=
  checkCasesFrom_step tree [5,5,5,5,5,6] 0 64 checked_type6_28_chunk0 (checkCasesFrom_step tree [5,5,5,5,5,6] 64 64 checked_type6_28_chunk64 (checkCasesFrom_step tree [5,5,5,5,5,6] 128 64 checked_type6_28_chunk128 (checked_type6_28_assembly_from192)))


end ThreeBoundEndpoint40Records


