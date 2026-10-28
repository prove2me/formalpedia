-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks045
-- name    : BS2_b3ba934b_Endpoint40RecordChecks045
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:16:39.20128+00:00
-- url     : https://prove2.me/theorems/5cb92632-46f7-418c-95ae-46b35242149d
-- title:
--   Sensitivity separation: Endpoint40RecordChecks045 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks045` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks045.lean; original SHA-256 474cb49888df652c1cdd66845a6b14d7f5b56cbd93fe0bf059b3f71150afaf2a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_13_chunk2048 : checkCasesChunk tree [2,5,5,5,5,5] 2048 64=true := by decide +kernel

theorem checked_type6_13_chunk2112 : checkCasesChunk tree [2,5,5,5,5,5] 2112 32=true := by decide +kernel

theorem checked_type6_14_chunk0 : checkCasesChunk tree [2,5,5,5,5,6] 0 64=true := by decide +kernel

theorem checked_type6_14_chunk64 : checkCasesChunk tree [2,5,5,5,5,6] 64 16=true := by decide +kernel

theorem checked_type6_15_chunk0 : checkCasesChunk tree [2,5,5,5,5,7] 0 64=true := by decide +kernel

theorem checked_type6_15_chunk64 : checkCasesChunk tree [2,5,5,5,5,7] 64 64=true := by decide +kernel

theorem checked_type6_15_chunk128 : checkCasesChunk tree [2,5,5,5,5,7] 128 64=true := by decide +kernel

theorem checked_type6_15_chunk192 : checkCasesChunk tree [2,5,5,5,5,7] 192 64=true := by decide +kernel

theorem checked_type6_15_chunk256 : checkCasesChunk tree [2,5,5,5,5,7] 256 64=true := by decide +kernel

theorem checked_type6_15_chunk320 : checkCasesChunk tree [2,5,5,5,5,7] 320 64=true := by decide +kernel

theorem checked_type6_15_chunk384 : checkCasesChunk tree [2,5,5,5,5,7] 384 64=true := by decide +kernel

theorem checked_type6_15_chunk448 : checkCasesChunk tree [2,5,5,5,5,7] 448 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_15_chunk448


