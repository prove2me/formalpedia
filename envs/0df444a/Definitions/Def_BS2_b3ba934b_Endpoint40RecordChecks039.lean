-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks039
-- name    : BS2_b3ba934b_Endpoint40RecordChecks039
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:11:20.707391+00:00
-- url     : https://prove2.me/theorems/f34575ff-7fc9-41f9-9244-a5eb8e785c52
-- title:
--   Sensitivity separation: Endpoint40RecordChecks039 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks039` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks039.lean; original SHA-256 b8eb389b0ad6ebd448e2bcd51a4230157a65581b1467df36ab16c375b3847ef5; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_4_chunk64 : checkCasesChunk tree [1,5,5,5,5,7] 64 16=true := by decide +kernel

theorem checked_type6_5_chunk0 : checkCasesChunk tree [2,2,2,5,5,5] 0 64=true := by decide +kernel

theorem checked_type6_5_chunk64 : checkCasesChunk tree [2,2,2,5,5,5] 64 64=true := by decide +kernel

theorem checked_type6_5_chunk128 : checkCasesChunk tree [2,2,2,5,5,5] 128 4=true := by decide +kernel

theorem checked_type6_6_chunk0 : checkCasesChunk tree [2,2,4,5,5,5] 0 64=true := by decide +kernel

theorem checked_type6_6_chunk64 : checkCasesChunk tree [2,2,4,5,5,5] 64 64=true := by decide +kernel

theorem checked_type6_6_chunk128 : checkCasesChunk tree [2,2,4,5,5,5] 128 4=true := by decide +kernel

theorem checked_type6_7_chunk0 : checkCasesChunk tree [2,2,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type6_7_chunk64 : checkCasesChunk tree [2,2,5,5,5,5] 64 64=true := by decide +kernel

theorem checked_type6_7_chunk128 : checkCasesChunk tree [2,2,5,5,5,5] 128 64=true := by decide +kernel

theorem checked_type6_7_chunk192 : checkCasesChunk tree [2,2,5,5,5,5] 192 64=true := by decide +kernel

theorem checked_type6_7_chunk256 : checkCasesChunk tree [2,2,5,5,5,5] 256 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_7_chunk256


