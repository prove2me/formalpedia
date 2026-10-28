-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl002
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl002
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T17:21:34.255801+00:00
-- url     : https://prove2.me/theorems/bd7a1781-913a-4ad7-a6b0-708a2500125c
-- title:
--   Sensitivity record composition: checked_type6_29_assembly_from1664
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_29_assembly_from1664, isolated as one complete proof with its original statement and proof bytes.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl001
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks062_Check06
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks062_Check07
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks062_Check08
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks062_Check09
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_29_assembly_from1664 : checkCasesFrom tree [5,5,5,5,5,7] 1664=true :=
  checkCasesFrom_step tree [5,5,5,5,5,7] 1664 64 checked_type6_29_chunk1664 (checkCasesFrom_step tree [5,5,5,5,5,7] 1728 64 checked_type6_29_chunk1728 (checkCasesFrom_step tree [5,5,5,5,5,7] 1792 64 checked_type6_29_chunk1792 (checkCasesFrom_step tree [5,5,5,5,5,7] 1856 64 checked_type6_29_chunk1856 (checked_type6_29_assembly_from1920))))


end ThreeBoundEndpoint40Records


