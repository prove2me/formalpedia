-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks028
-- name    : BS2_b3ba934b_Endpoint40RecordChecks028
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:05:03.729257+00:00
-- url     : https://prove2.me/theorems/10b99709-0f07-4eb6-b65e-87f9d69eb8a3
-- title:
--   Sensitivity separation: Endpoint40RecordChecks028 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks028` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks028.lean; original SHA-256 f55964cb94964af2b97d33f3edde7131fa3a056364bbb940649c3bf01fef6fdb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_96_chunk128 : checkCasesChunk tree [2,5,5,5,7] 128 64=true := by decide +kernel

theorem checked_type5_96_chunk192 : checkCasesChunk tree [2,5,5,5,7] 192 64=true := by decide +kernel

theorem checked_type5_96_chunk256 : checkCasesChunk tree [2,5,5,5,7] 256 48=true := by decide +kernel

theorem checked_type5_97 : checkTypes tree [2,5,5,6,6]=true := by decide +kernel

theorem checked_type5_98 : checkTypes tree [2,5,5,6,7]=true := by decide +kernel

theorem checked_type5_99_chunk0 : checkCasesChunk tree [2,5,5,7,7] 0 64=true := by decide +kernel

theorem checked_type5_99_chunk64 : checkCasesChunk tree [2,5,5,7,7] 64 64=true := by decide +kernel

theorem checked_type5_99_chunk128 : checkCasesChunk tree [2,5,5,7,7] 128 44=true := by decide +kernel

theorem checked_type5_100 : checkTypes tree [2,5,6,7,7]=true := by decide +kernel

theorem checked_type5_101_chunk0 : checkCasesChunk tree [2,5,7,7,7] 0 64=true := by decide +kernel

theorem checked_type5_101_chunk64 : checkCasesChunk tree [2,5,7,7,7] 64 16=true := by decide +kernel

theorem checked_type5_102 : checkTypes tree [2,7,7,7,7]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_102


