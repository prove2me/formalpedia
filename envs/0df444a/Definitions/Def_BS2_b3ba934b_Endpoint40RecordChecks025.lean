-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks025
-- name    : BS2_b3ba934b_Endpoint40RecordChecks025
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:03:50.020025+00:00
-- url     : https://prove2.me/theorems/7877ab9a-5748-4173-aa60-67b2c44fd60f
-- title:
--   Sensitivity separation: Endpoint40RecordChecks025 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks025` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks025.lean; original SHA-256 c511ac87460fd9e9560687aca67fe009531af352ad8b49d41a8e9804612c933c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_81 : checkTypes tree [2,4,4,4,4]=true := by decide +kernel

theorem checked_type5_82_chunk0 : checkCasesChunk tree [2,4,4,4,5] 0 64=true := by decide +kernel

theorem checked_type5_82_chunk64 : checkCasesChunk tree [2,4,4,4,5] 64 16=true := by decide +kernel

theorem checked_type5_83 : checkTypes tree [2,4,4,4,7]=true := by decide +kernel

theorem checked_type5_84_chunk0 : checkCasesChunk tree [2,4,4,5,5] 0 64=true := by decide +kernel

theorem checked_type5_84_chunk64 : checkCasesChunk tree [2,4,4,5,5] 64 64=true := by decide +kernel

theorem checked_type5_84_chunk128 : checkCasesChunk tree [2,4,4,5,5] 128 44=true := by decide +kernel

theorem checked_type5_85 : checkTypes tree [2,4,4,5,6]=true := by decide +kernel

theorem checked_type5_86_chunk0 : checkCasesChunk tree [2,4,4,5,7] 0 64=true := by decide +kernel

theorem checked_type5_86_chunk64 : checkCasesChunk tree [2,4,4,5,7] 64 16=true := by decide +kernel

theorem checked_type5_87 : checkTypes tree [2,4,4,7,7]=true := by decide +kernel

theorem checked_type5_88_chunk0 : checkCasesChunk tree [2,4,5,5,5] 0 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_88_chunk0


