-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks029
-- name    : BS2_b3ba934b_Endpoint40RecordChecks029
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:05:50.96199+00:00
-- url     : https://prove2.me/theorems/2e6fd63b-9a4a-4a65-b7bd-6872c23f15d5
-- title:
--   Sensitivity separation: Endpoint40RecordChecks029 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks029` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks029.lean; original SHA-256 d1175295657d2d1e4793f32b30dab57564730fa4e8b2fd131653355ba8ee2a1a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_103 : checkTypes tree [3,3,4,5,5]=true := by decide +kernel

theorem checked_type5_104 : checkTypes tree [3,3,5,5,5]=true := by decide +kernel

theorem checked_type5_105 : checkTypes tree [3,3,5,5,7]=true := by decide +kernel

theorem checked_type5_106 : checkTypes tree [3,4,4,4,5]=true := by decide +kernel

theorem checked_type5_107 : checkTypes tree [3,4,4,5,5]=true := by decide +kernel

theorem checked_type5_108 : checkTypes tree [3,4,4,5,7]=true := by decide +kernel

theorem checked_type5_109_chunk0 : checkCasesChunk tree [3,4,5,5,5] 0 64=true := by decide +kernel

theorem checked_type5_109_chunk64 : checkCasesChunk tree [3,4,5,5,5] 64 42=true := by decide +kernel

theorem checked_type5_110 : checkTypes tree [3,4,5,5,6]=true := by decide +kernel

theorem checked_type5_111 : checkTypes tree [3,4,5,5,7]=true := by decide +kernel

theorem checked_type5_112 : checkTypes tree [3,4,5,7,7]=true := by decide +kernel

theorem checked_type5_113_chunk0 : checkCasesChunk tree [3,5,5,5,5] 0 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_113_chunk0


