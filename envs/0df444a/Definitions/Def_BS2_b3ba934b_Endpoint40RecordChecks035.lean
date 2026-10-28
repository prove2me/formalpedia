-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks035
-- name    : BS2_b3ba934b_Endpoint40RecordChecks035
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:09:22.109847+00:00
-- url     : https://prove2.me/theorems/cd536cb2-c14c-4113-8e0f-b76cf988433f
-- title:
--   Sensitivity separation: Endpoint40RecordChecks035 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks035` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks035.lean; original SHA-256 b00f33c81687361633a97bfc49be19f965d85f695f0af46a32344ceca6d0d87b; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_141_chunk256 : checkCasesChunk tree [5,5,5,5,5] 256 64=true := by decide +kernel

theorem checked_type5_141_chunk320 : checkCasesChunk tree [5,5,5,5,5] 320 64=true := by decide +kernel

theorem checked_type5_141_chunk384 : checkCasesChunk tree [5,5,5,5,5] 384 64=true := by decide +kernel

theorem checked_type5_141_chunk448 : checkCasesChunk tree [5,5,5,5,5] 448 64=true := by decide +kernel

theorem checked_type5_141_chunk512 : checkCasesChunk tree [5,5,5,5,5] 512 64=true := by decide +kernel

theorem checked_type5_141_chunk576 : checkCasesChunk tree [5,5,5,5,5] 576 64=true := by decide +kernel

theorem checked_type5_141_chunk640 : checkCasesChunk tree [5,5,5,5,5] 640 64=true := by decide +kernel

theorem checked_type5_142_chunk0 : checkCasesChunk tree [5,5,5,5,6] 0 64=true := by decide +kernel

theorem checked_type5_142_chunk64 : checkCasesChunk tree [5,5,5,5,6] 64 64=true := by decide +kernel

theorem checked_type5_142_chunk128 : checkCasesChunk tree [5,5,5,5,6] 128 64=true := by decide +kernel

theorem checked_type5_143_chunk0 : checkCasesChunk tree [5,5,5,5,7] 0 64=true := by decide +kernel

theorem checked_type5_143_chunk64 : checkCasesChunk tree [5,5,5,5,7] 64 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_143_chunk64


