-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks041
-- name    : BS2_b3ba934b_Endpoint40RecordChecks041
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:13:24.578715+00:00
-- url     : https://prove2.me/theorems/fbc5d182-cf98-4a57-99ce-8709e2681be1
-- title:
--   Sensitivity separation: Endpoint40RecordChecks041 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks041` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks041.lean; original SHA-256 3f0930c847bf80c625386ebea3c7d7239ce19e710b8c3faa3a1c89ba60734791; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_10_chunk64 : checkCasesChunk tree [2,4,4,5,5,5] 64 64=true := by decide +kernel

theorem checked_type6_10_chunk128 : checkCasesChunk tree [2,4,4,5,5,5] 128 4=true := by decide +kernel

theorem checked_type6_11_chunk0 : checkCasesChunk tree [2,4,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type6_11_chunk64 : checkCasesChunk tree [2,4,5,5,5,5] 64 64=true := by decide +kernel

theorem checked_type6_11_chunk128 : checkCasesChunk tree [2,4,5,5,5,5] 128 64=true := by decide +kernel

theorem checked_type6_11_chunk192 : checkCasesChunk tree [2,4,5,5,5,5] 192 64=true := by decide +kernel

theorem checked_type6_11_chunk256 : checkCasesChunk tree [2,4,5,5,5,5] 256 64=true := by decide +kernel

theorem checked_type6_11_chunk320 : checkCasesChunk tree [2,4,5,5,5,5] 320 64=true := by decide +kernel

theorem checked_type6_11_chunk384 : checkCasesChunk tree [2,4,5,5,5,5] 384 64=true := by decide +kernel

theorem checked_type6_11_chunk448 : checkCasesChunk tree [2,4,5,5,5,5] 448 64=true := by decide +kernel

theorem checked_type6_11_chunk512 : checkCasesChunk tree [2,4,5,5,5,5] 512 64=true := by decide +kernel

theorem checked_type6_11_chunk576 : checkCasesChunk tree [2,4,5,5,5,5] 576 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_11_chunk576


