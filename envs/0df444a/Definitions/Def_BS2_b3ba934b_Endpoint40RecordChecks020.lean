-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks020
-- name    : BS2_b3ba934b_Endpoint40RecordChecks020
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:55:46.267986+00:00
-- url     : https://prove2.me/theorems/bc0a2a71-dbe7-49ed-a06c-054f32ce588c
-- title:
--   Sensitivity separation: Endpoint40RecordChecks020 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks020` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks020.lean; original SHA-256 9950ff0914ff82962e1f19720016d60be87b0713142519caefc010905643f295; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_39_chunk128 : checkCasesChunk tree [1,5,5,5,5] 128 64=true := by decide +kernel

theorem checked_type5_40 : checkTypes tree [1,5,5,5,6]=true := by decide +kernel

theorem checked_type5_41_chunk0 : checkCasesChunk tree [1,5,5,5,7] 0 64=true := by decide +kernel

theorem checked_type5_41_chunk64 : checkCasesChunk tree [1,5,5,5,7] 64 42=true := by decide +kernel

theorem checked_type5_42 : checkTypes tree [1,5,5,6,7]=true := by decide +kernel

theorem checked_type5_43 : checkTypes tree [1,5,5,7,7]=true := by decide +kernel

theorem checked_type5_44 : checkTypes tree [1,5,7,7,7]=true := by decide +kernel

theorem checked_type5_45 : checkTypes tree [2,2,2,2,2]=true := by decide +kernel

theorem checked_type5_46 : checkTypes tree [2,2,2,2,4]=true := by decide +kernel

theorem checked_type5_47_chunk0 : checkCasesChunk tree [2,2,2,2,5] 0 64=true := by decide +kernel

theorem checked_type5_47_chunk64 : checkCasesChunk tree [2,2,2,2,5] 64 16=true := by decide +kernel

theorem checked_type5_48 : checkTypes tree [2,2,2,2,7]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_48


