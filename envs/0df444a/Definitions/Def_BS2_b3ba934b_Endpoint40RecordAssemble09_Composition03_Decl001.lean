-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl001
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl001
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T17:09:08.769997+00:00
-- url     : https://prove2.me/theorems/ad5184f3-5d0a-411b-8f4c-a16423a305d9
-- title:
--   Sensitivity record composition: checked_type6_29_assembly_from1920
-- statement:
--   The unchanged checked theorem ThreeBoundEndpoint40Records.checked_type6_29_assembly_from1920, isolated as one complete proof with its original statement and proof bytes.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition03_Decl000
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks062_Check10
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks062_Check11
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks063_Check00
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks063_Check01
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_29_assembly_from1920 : checkCasesFrom tree [5,5,5,5,5,7] 1920=true :=
  checkCasesFrom_step tree [5,5,5,5,5,7] 1920 64 checked_type6_29_chunk1920 (checkCasesFrom_step tree [5,5,5,5,5,7] 1984 64 checked_type6_29_chunk1984 (checkCasesFrom_step tree [5,5,5,5,5,7] 2048 64 checked_type6_29_chunk2048 (checkCasesFrom_step tree [5,5,5,5,5,7] 2112 32 checked_type6_29_chunk2112 (checked_type6_29_assembly_end))))


end ThreeBoundEndpoint40Records


