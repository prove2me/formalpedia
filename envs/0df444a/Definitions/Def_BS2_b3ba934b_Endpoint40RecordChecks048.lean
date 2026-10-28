-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks048
-- name    : BS2_b3ba934b_Endpoint40RecordChecks048
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:18:29.083017+00:00
-- url     : https://prove2.me/theorems/e2343ae8-61dc-41c0-a249-525fee2dd979
-- title:
--   Sensitivity separation: Endpoint40RecordChecks048 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks048` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks048.lean; original SHA-256 9dac806cb836da8a8847898f54269c9e387bd9783106b49e77b9d2051699fd8d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_21_chunk256 : checkCasesChunk tree [4,4,5,5,5,5] 256 64=true := by decide +kernel

theorem checked_type6_21_chunk320 : checkCasesChunk tree [4,4,5,5,5,5] 320 64=true := by decide +kernel

theorem checked_type6_21_chunk384 : checkCasesChunk tree [4,4,5,5,5,5] 384 64=true := by decide +kernel

theorem checked_type6_21_chunk448 : checkCasesChunk tree [4,4,5,5,5,5] 448 64=true := by decide +kernel

theorem checked_type6_21_chunk512 : checkCasesChunk tree [4,4,5,5,5,5] 512 64=true := by decide +kernel

theorem checked_type6_21_chunk576 : checkCasesChunk tree [4,4,5,5,5,5] 576 64=true := by decide +kernel

theorem checked_type6_21_chunk640 : checkCasesChunk tree [4,4,5,5,5,5] 640 48=true := by decide +kernel

theorem checked_type6_22_chunk0 : checkCasesChunk tree [4,4,5,5,5,7] 0 64=true := by decide +kernel

theorem checked_type6_22_chunk64 : checkCasesChunk tree [4,4,5,5,5,7] 64 64=true := by decide +kernel

theorem checked_type6_22_chunk128 : checkCasesChunk tree [4,4,5,5,5,7] 128 4=true := by decide +kernel

theorem checked_type6_23_chunk0 : checkCasesChunk tree [4,5,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type6_23_chunk64 : checkCasesChunk tree [4,5,5,5,5,5] 64 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_23_chunk64


