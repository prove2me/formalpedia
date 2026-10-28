-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks043
-- name    : BS2_b3ba934b_Endpoint40RecordChecks043
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:15:54.82985+00:00
-- url     : https://prove2.me/theorems/b0fc9aa6-6dfa-4c47-a925-6b54eb2ed49d
-- title:
--   Sensitivity separation: Endpoint40RecordChecks043 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks043` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks043.lean; original SHA-256 99e26f4a96384f9bc5b663e95114575b1bb378475e516a54e811fc7fdeab381a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_13_chunk512 : checkCasesChunk tree [2,5,5,5,5,5] 512 64=true := by decide +kernel

theorem checked_type6_13_chunk576 : checkCasesChunk tree [2,5,5,5,5,5] 576 64=true := by decide +kernel

theorem checked_type6_13_chunk640 : checkCasesChunk tree [2,5,5,5,5,5] 640 64=true := by decide +kernel

theorem checked_type6_13_chunk704 : checkCasesChunk tree [2,5,5,5,5,5] 704 64=true := by decide +kernel

theorem checked_type6_13_chunk768 : checkCasesChunk tree [2,5,5,5,5,5] 768 64=true := by decide +kernel

theorem checked_type6_13_chunk832 : checkCasesChunk tree [2,5,5,5,5,5] 832 64=true := by decide +kernel

theorem checked_type6_13_chunk896 : checkCasesChunk tree [2,5,5,5,5,5] 896 64=true := by decide +kernel

theorem checked_type6_13_chunk960 : checkCasesChunk tree [2,5,5,5,5,5] 960 64=true := by decide +kernel

theorem checked_type6_13_chunk1024 : checkCasesChunk tree [2,5,5,5,5,5] 1024 64=true := by decide +kernel

theorem checked_type6_13_chunk1088 : checkCasesChunk tree [2,5,5,5,5,5] 1088 64=true := by decide +kernel

theorem checked_type6_13_chunk1152 : checkCasesChunk tree [2,5,5,5,5,5] 1152 64=true := by decide +kernel

theorem checked_type6_13_chunk1216 : checkCasesChunk tree [2,5,5,5,5,5] 1216 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_13_chunk1216


