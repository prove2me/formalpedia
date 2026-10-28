-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks031
-- name    : BS2_b3ba934b_Endpoint40RecordChecks031
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:06:56.099279+00:00
-- url     : https://prove2.me/theorems/6947481e-4033-4a11-9585-eb103267bebf
-- title:
--   Sensitivity separation: Endpoint40RecordChecks031 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks031` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks031.lean; original SHA-256 45559b0df751a06bad635ec33d691d5fda840647d3b8d7b4c36975e7277f0d7b; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_122_chunk0 : checkCasesChunk tree [4,4,4,5,5] 0 64=true := by decide +kernel

theorem checked_type5_122_chunk64 : checkCasesChunk tree [4,4,4,5,5] 64 64=true := by decide +kernel

theorem checked_type5_122_chunk128 : checkCasesChunk tree [4,4,4,5,5] 128 44=true := by decide +kernel

theorem checked_type5_123 : checkTypes tree [4,4,4,5,6]=true := by decide +kernel

theorem checked_type5_124_chunk0 : checkCasesChunk tree [4,4,4,5,7] 0 64=true := by decide +kernel

theorem checked_type5_124_chunk64 : checkCasesChunk tree [4,4,4,5,7] 64 16=true := by decide +kernel

theorem checked_type5_125 : checkTypes tree [4,4,4,7,7]=true := by decide +kernel

theorem checked_type5_126_chunk0 : checkCasesChunk tree [4,4,5,5,5] 0 64=true := by decide +kernel

theorem checked_type5_126_chunk64 : checkCasesChunk tree [4,4,5,5,5] 64 64=true := by decide +kernel

theorem checked_type5_126_chunk128 : checkCasesChunk tree [4,4,5,5,5] 128 64=true := by decide +kernel

theorem checked_type5_126_chunk192 : checkCasesChunk tree [4,4,5,5,5] 192 64=true := by decide +kernel

theorem checked_type5_126_chunk256 : checkCasesChunk tree [4,4,5,5,5] 256 48=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_126_chunk256


