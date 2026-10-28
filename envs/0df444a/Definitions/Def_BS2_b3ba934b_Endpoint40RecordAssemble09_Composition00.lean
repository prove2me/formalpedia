-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble09_Composition00
-- name    : BS2_b3ba934b_Endpoint40RecordAssemble09_Composition00
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:42:31.679494+00:00
-- url     : https://prove2.me/theorems/8ea300f8-7395-4527-bb4b-21b726b91f11
-- title:
--   Sensitivity separation: Endpoint40RecordAssemble09 proof composition 1
-- statement:
--   Proves the unchanged original statement ThreeBoundEndpoint40Records.checked_type6_26 using the original accepted certificate checks, original kernel decisions, and small opaque structural lemmas.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordAssemble09.lean; original SHA-256 53823f851a266487908c8736d711f23ee98517f598c93fb29c94568a87f671a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks052
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_26_assembly_end : checkCasesFrom tree [4,5,5,5,7,7] 132=true :=
  checkCasesFrom_end tree [4,5,5,5,7,7] 132 (by decide +kernel)

theorem checked_type6_26_assembly_from0 : checkCasesFrom tree [4,5,5,5,7,7] 0=true :=
  checkCasesFrom_step tree [4,5,5,5,7,7] 0 64 checked_type6_26_chunk0 (checkCasesFrom_step tree [4,5,5,5,7,7] 64 64 checked_type6_26_chunk64 (checkCasesFrom_step tree [4,5,5,5,7,7] 128 4 checked_type6_26_chunk128 (checked_type6_26_assembly_end)))

theorem checked_type6_26 : checkTypes tree [4,5,5,5,7,7]=true :=
  checkTypes_of_from tree [4,5,5,5,7,7] checked_type6_26_assembly_from0

end ThreeBoundEndpoint40Records


