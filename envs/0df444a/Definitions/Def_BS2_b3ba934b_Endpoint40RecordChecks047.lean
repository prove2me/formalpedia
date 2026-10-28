-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks047
-- name    : BS2_b3ba934b_Endpoint40RecordChecks047
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:18:18.52021+00:00
-- url     : https://prove2.me/theorems/8685582e-3459-4b3e-a8df-90a7e5c63f4a
-- title:
--   Sensitivity separation: Endpoint40RecordChecks047 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks047` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks047.lean; original SHA-256 fd8ef8694c0fdf8c74d0532af7bb39225c48e2f7b507fed4c8e60cb9efec2139; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_18_chunk256 : checkCasesChunk tree [3,5,5,5,5,5] 256 64=true := by decide +kernel

theorem checked_type6_18_chunk320 : checkCasesChunk tree [3,5,5,5,5,5] 320 64=true := by decide +kernel

theorem checked_type6_18_chunk384 : checkCasesChunk tree [3,5,5,5,5,5] 384 40=true := by decide +kernel

theorem checked_type6_19_chunk0 : checkCasesChunk tree [3,5,5,5,5,7] 0 64=true := by decide +kernel

theorem checked_type6_19_chunk64 : checkCasesChunk tree [3,5,5,5,5,7] 64 16=true := by decide +kernel

theorem checked_type6_20_chunk0 : checkCasesChunk tree [4,4,4,5,5,5] 0 64=true := by decide +kernel

theorem checked_type6_20_chunk64 : checkCasesChunk tree [4,4,4,5,5,5] 64 64=true := by decide +kernel

theorem checked_type6_20_chunk128 : checkCasesChunk tree [4,4,4,5,5,5] 128 4=true := by decide +kernel

theorem checked_type6_21_chunk0 : checkCasesChunk tree [4,4,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type6_21_chunk64 : checkCasesChunk tree [4,4,5,5,5,5] 64 64=true := by decide +kernel

theorem checked_type6_21_chunk128 : checkCasesChunk tree [4,4,5,5,5,5] 128 64=true := by decide +kernel

theorem checked_type6_21_chunk192 : checkCasesChunk tree [4,4,5,5,5,5] 192 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_21_chunk192


