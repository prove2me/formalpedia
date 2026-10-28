-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks053
-- name    : BS2_b3ba934b_Endpoint40RecordChecks053
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:28:54.440845+00:00
-- url     : https://prove2.me/theorems/6b37017e-b313-4302-a40d-19a008e614fb
-- title:
--   Sensitivity separation: Endpoint40RecordChecks053 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks053` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks053.lean; original SHA-256 78001f20b9146162220e126b15baaa4de03220d451f088ae1fe72ce04bb8e033; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_27_chunk0 : checkCasesChunk tree [5,5,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type6_27_chunk64 : checkCasesChunk tree [5,5,5,5,5,5] 64 64=true := by decide +kernel

theorem checked_type6_27_chunk128 : checkCasesChunk tree [5,5,5,5,5,5] 128 64=true := by decide +kernel

theorem checked_type6_27_chunk192 : checkCasesChunk tree [5,5,5,5,5,5] 192 64=true := by decide +kernel

theorem checked_type6_27_chunk256 : checkCasesChunk tree [5,5,5,5,5,5] 256 64=true := by decide +kernel

theorem checked_type6_27_chunk320 : checkCasesChunk tree [5,5,5,5,5,5] 320 64=true := by decide +kernel

theorem checked_type6_27_chunk384 : checkCasesChunk tree [5,5,5,5,5,5] 384 64=true := by decide +kernel

theorem checked_type6_27_chunk448 : checkCasesChunk tree [5,5,5,5,5,5] 448 64=true := by decide +kernel

theorem checked_type6_27_chunk512 : checkCasesChunk tree [5,5,5,5,5,5] 512 64=true := by decide +kernel

theorem checked_type6_27_chunk576 : checkCasesChunk tree [5,5,5,5,5,5] 576 64=true := by decide +kernel

theorem checked_type6_27_chunk640 : checkCasesChunk tree [5,5,5,5,5,5] 640 64=true := by decide +kernel

theorem checked_type6_27_chunk704 : checkCasesChunk tree [5,5,5,5,5,5] 704 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_27_chunk704


