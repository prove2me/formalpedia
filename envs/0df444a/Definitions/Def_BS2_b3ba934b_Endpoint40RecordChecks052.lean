-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks052
-- name    : BS2_b3ba934b_Endpoint40RecordChecks052
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:23:40.370844+00:00
-- url     : https://prove2.me/theorems/44a0fa5f-cdd4-416a-983e-3353451d089c
-- title:
--   Sensitivity separation: Endpoint40RecordChecks052 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks052` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks052.lean; original SHA-256 68ddc69fb56dcd325516197935d9da337ed6470d39f5f73ad32cd0bfb854504e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_25_chunk128 : checkCasesChunk tree [4,5,5,5,5,7] 128 64=true := by decide +kernel

theorem checked_type6_25_chunk192 : checkCasesChunk tree [4,5,5,5,5,7] 192 64=true := by decide +kernel

theorem checked_type6_25_chunk256 : checkCasesChunk tree [4,5,5,5,5,7] 256 64=true := by decide +kernel

theorem checked_type6_25_chunk320 : checkCasesChunk tree [4,5,5,5,5,7] 320 64=true := by decide +kernel

theorem checked_type6_25_chunk384 : checkCasesChunk tree [4,5,5,5,5,7] 384 64=true := by decide +kernel

theorem checked_type6_25_chunk448 : checkCasesChunk tree [4,5,5,5,5,7] 448 64=true := by decide +kernel

theorem checked_type6_25_chunk512 : checkCasesChunk tree [4,5,5,5,5,7] 512 64=true := by decide +kernel

theorem checked_type6_25_chunk576 : checkCasesChunk tree [4,5,5,5,5,7] 576 64=true := by decide +kernel

theorem checked_type6_25_chunk640 : checkCasesChunk tree [4,5,5,5,5,7] 640 48=true := by decide +kernel

theorem checked_type6_26_chunk0 : checkCasesChunk tree [4,5,5,5,7,7] 0 64=true := by decide +kernel

theorem checked_type6_26_chunk64 : checkCasesChunk tree [4,5,5,5,7,7] 64 64=true := by decide +kernel

theorem checked_type6_26_chunk128 : checkCasesChunk tree [4,5,5,5,7,7] 128 4=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_26_chunk128


