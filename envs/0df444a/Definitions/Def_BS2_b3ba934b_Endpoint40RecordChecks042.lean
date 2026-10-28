-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks042
-- name    : BS2_b3ba934b_Endpoint40RecordChecks042
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:14:11.161608+00:00
-- url     : https://prove2.me/theorems/a7119c2d-df9f-429f-8e49-ed9feac8c3d4
-- title:
--   Sensitivity separation: Endpoint40RecordChecks042 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks042` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks042.lean; original SHA-256 c0e987ed24c0173d7e1c45b5b3f0666107f98a802adcbc00a71b3d1409bc9e3a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_11_chunk640 : checkCasesChunk tree [2,4,5,5,5,5] 640 48=true := by decide +kernel

theorem checked_type6_12_chunk0 : checkCasesChunk tree [2,4,5,5,5,7] 0 64=true := by decide +kernel

theorem checked_type6_12_chunk64 : checkCasesChunk tree [2,4,5,5,5,7] 64 64=true := by decide +kernel

theorem checked_type6_12_chunk128 : checkCasesChunk tree [2,4,5,5,5,7] 128 4=true := by decide +kernel

theorem checked_type6_13_chunk0 : checkCasesChunk tree [2,5,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type6_13_chunk64 : checkCasesChunk tree [2,5,5,5,5,5] 64 64=true := by decide +kernel

theorem checked_type6_13_chunk128 : checkCasesChunk tree [2,5,5,5,5,5] 128 64=true := by decide +kernel

theorem checked_type6_13_chunk192 : checkCasesChunk tree [2,5,5,5,5,5] 192 64=true := by decide +kernel

theorem checked_type6_13_chunk256 : checkCasesChunk tree [2,5,5,5,5,5] 256 64=true := by decide +kernel

theorem checked_type6_13_chunk320 : checkCasesChunk tree [2,5,5,5,5,5] 320 64=true := by decide +kernel

theorem checked_type6_13_chunk384 : checkCasesChunk tree [2,5,5,5,5,5] 384 64=true := by decide +kernel

theorem checked_type6_13_chunk448 : checkCasesChunk tree [2,5,5,5,5,5] 448 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_13_chunk448


