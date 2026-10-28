-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks036
-- name    : BS2_b3ba934b_Endpoint40RecordChecks036
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:09:44.61751+00:00
-- url     : https://prove2.me/theorems/b4a3b390-df6a-4665-83c5-d757725a81e1
-- title:
--   Sensitivity separation: Endpoint40RecordChecks036 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks036` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks036.lean; original SHA-256 dc1ceca6ce3d92e8de4a12ec88a19728aacf74753b03eb85bc24dee2d8be5932; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_143_chunk128 : checkCasesChunk tree [5,5,5,5,7] 128 64=true := by decide +kernel

theorem checked_type5_143_chunk192 : checkCasesChunk tree [5,5,5,5,7] 192 64=true := by decide +kernel

theorem checked_type5_143_chunk256 : checkCasesChunk tree [5,5,5,5,7] 256 64=true := by decide +kernel

theorem checked_type5_143_chunk320 : checkCasesChunk tree [5,5,5,5,7] 320 64=true := by decide +kernel

theorem checked_type5_143_chunk384 : checkCasesChunk tree [5,5,5,5,7] 384 64=true := by decide +kernel

theorem checked_type5_143_chunk448 : checkCasesChunk tree [5,5,5,5,7] 448 32=true := by decide +kernel

theorem checked_type5_144 : checkTypes tree [5,5,5,6,6]=true := by decide +kernel

theorem checked_type5_145_chunk0 : checkCasesChunk tree [5,5,5,6,7] 0 64=true := by decide +kernel

theorem checked_type5_145_chunk64 : checkCasesChunk tree [5,5,5,6,7] 64 42=true := by decide +kernel

theorem checked_type5_146_chunk0 : checkCasesChunk tree [5,5,5,7,7] 0 64=true := by decide +kernel

theorem checked_type5_146_chunk64 : checkCasesChunk tree [5,5,5,7,7] 64 64=true := by decide +kernel

theorem checked_type5_146_chunk128 : checkCasesChunk tree [5,5,5,7,7] 128 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_146_chunk128


