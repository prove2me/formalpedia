-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks049
-- name    : BS2_b3ba934b_Endpoint40RecordChecks049
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:20:53.602632+00:00
-- url     : https://prove2.me/theorems/8f6ef7f4-9a0b-42f7-80bd-a98e7e28a22f
-- title:
--   Sensitivity separation: Endpoint40RecordChecks049 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks049` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks049.lean; original SHA-256 0640e398d0b0d419f716f499a32aef3c10ba33ef1eefbdd81aa569dd0398cdf5; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_23_chunk128 : checkCasesChunk tree [4,5,5,5,5,5] 128 64=true := by decide +kernel

theorem checked_type6_23_chunk192 : checkCasesChunk tree [4,5,5,5,5,5] 192 64=true := by decide +kernel

theorem checked_type6_23_chunk256 : checkCasesChunk tree [4,5,5,5,5,5] 256 64=true := by decide +kernel

theorem checked_type6_23_chunk320 : checkCasesChunk tree [4,5,5,5,5,5] 320 64=true := by decide +kernel

theorem checked_type6_23_chunk384 : checkCasesChunk tree [4,5,5,5,5,5] 384 64=true := by decide +kernel

theorem checked_type6_23_chunk448 : checkCasesChunk tree [4,5,5,5,5,5] 448 64=true := by decide +kernel

theorem checked_type6_23_chunk512 : checkCasesChunk tree [4,5,5,5,5,5] 512 64=true := by decide +kernel

theorem checked_type6_23_chunk576 : checkCasesChunk tree [4,5,5,5,5,5] 576 64=true := by decide +kernel

theorem checked_type6_23_chunk640 : checkCasesChunk tree [4,5,5,5,5,5] 640 64=true := by decide +kernel

theorem checked_type6_23_chunk704 : checkCasesChunk tree [4,5,5,5,5,5] 704 64=true := by decide +kernel

theorem checked_type6_23_chunk768 : checkCasesChunk tree [4,5,5,5,5,5] 768 64=true := by decide +kernel

theorem checked_type6_23_chunk832 : checkCasesChunk tree [4,5,5,5,5,5] 832 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_23_chunk832


