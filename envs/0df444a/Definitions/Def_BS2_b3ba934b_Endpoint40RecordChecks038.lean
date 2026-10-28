-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks038
-- name    : BS2_b3ba934b_Endpoint40RecordChecks038
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:13:02.722662+00:00
-- url     : https://prove2.me/theorems/cee61978-2456-47ed-a61d-5d8ed48d0db6
-- title:
--   Sensitivity separation: Endpoint40RecordChecks038 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks038` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks038.lean; original SHA-256 b5e5bd6b8592f0dbcf4f1adcc8041c294898f7c8b6aae4489ddb943d40d52220; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_1_chunk0 : checkCasesChunk tree [1,2,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type6_1_chunk64 : checkCasesChunk tree [1,2,5,5,5,5] 64 16=true := by decide +kernel

theorem checked_type6_2_chunk0 : checkCasesChunk tree [1,4,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type6_2_chunk64 : checkCasesChunk tree [1,4,5,5,5,5] 64 16=true := by decide +kernel

theorem checked_type6_3_chunk0 : checkCasesChunk tree [1,5,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type6_3_chunk64 : checkCasesChunk tree [1,5,5,5,5,5] 64 64=true := by decide +kernel

theorem checked_type6_3_chunk128 : checkCasesChunk tree [1,5,5,5,5,5] 128 64=true := by decide +kernel

theorem checked_type6_3_chunk192 : checkCasesChunk tree [1,5,5,5,5,5] 192 64=true := by decide +kernel

theorem checked_type6_3_chunk256 : checkCasesChunk tree [1,5,5,5,5,5] 256 64=true := by decide +kernel

theorem checked_type6_3_chunk320 : checkCasesChunk tree [1,5,5,5,5,5] 320 64=true := by decide +kernel

theorem checked_type6_3_chunk384 : checkCasesChunk tree [1,5,5,5,5,5] 384 40=true := by decide +kernel

theorem checked_type6_4_chunk0 : checkCasesChunk tree [1,5,5,5,5,7] 0 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_4_chunk0


