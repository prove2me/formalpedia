-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks040
-- name    : BS2_b3ba934b_Endpoint40RecordChecks040
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:12:15.409776+00:00
-- url     : https://prove2.me/theorems/44cf64b7-6d3b-4631-a0d7-0b46a8577700
-- title:
--   Sensitivity separation: Endpoint40RecordChecks040 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks040` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks040.lean; original SHA-256 80dde39b497c90467df8046f3bd172db15e3cea5b1fb40a53900f6fd62ce6f0e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_7_chunk320 : checkCasesChunk tree [2,2,5,5,5,5] 320 64=true := by decide +kernel

theorem checked_type6_7_chunk384 : checkCasesChunk tree [2,2,5,5,5,5] 384 64=true := by decide +kernel

theorem checked_type6_7_chunk448 : checkCasesChunk tree [2,2,5,5,5,5] 448 64=true := by decide +kernel

theorem checked_type6_7_chunk512 : checkCasesChunk tree [2,2,5,5,5,5] 512 64=true := by decide +kernel

theorem checked_type6_7_chunk576 : checkCasesChunk tree [2,2,5,5,5,5] 576 64=true := by decide +kernel

theorem checked_type6_7_chunk640 : checkCasesChunk tree [2,2,5,5,5,5] 640 48=true := by decide +kernel

theorem checked_type6_8_chunk0 : checkCasesChunk tree [2,2,5,5,5,7] 0 64=true := by decide +kernel

theorem checked_type6_8_chunk64 : checkCasesChunk tree [2,2,5,5,5,7] 64 64=true := by decide +kernel

theorem checked_type6_8_chunk128 : checkCasesChunk tree [2,2,5,5,5,7] 128 4=true := by decide +kernel

theorem checked_type6_9_chunk0 : checkCasesChunk tree [2,3,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type6_9_chunk64 : checkCasesChunk tree [2,3,5,5,5,5] 64 16=true := by decide +kernel

theorem checked_type6_10_chunk0 : checkCasesChunk tree [2,4,4,5,5,5] 0 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_10_chunk0


