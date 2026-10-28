-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks030
-- name    : BS2_b3ba934b_Endpoint40RecordChecks030
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:07:15.359589+00:00
-- url     : https://prove2.me/theorems/57fd23e9-8564-4723-917b-5035b5cf66b6
-- title:
--   Sensitivity separation: Endpoint40RecordChecks030 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks030` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks030.lean; original SHA-256 a75aa78ef31f612b3e7f0c688acbc4fb1e190a20834cc73306ef64788d8aab43; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_113_chunk64 : checkCasesChunk tree [3,5,5,5,5] 64 64=true := by decide +kernel

theorem checked_type5_113_chunk128 : checkCasesChunk tree [3,5,5,5,5] 128 64=true := by decide +kernel

theorem checked_type5_114 : checkTypes tree [3,5,5,5,6]=true := by decide +kernel

theorem checked_type5_115_chunk0 : checkCasesChunk tree [3,5,5,5,7] 0 64=true := by decide +kernel

theorem checked_type5_115_chunk64 : checkCasesChunk tree [3,5,5,5,7] 64 42=true := by decide +kernel

theorem checked_type5_116 : checkTypes tree [3,5,5,6,7]=true := by decide +kernel

theorem checked_type5_117 : checkTypes tree [3,5,5,7,7]=true := by decide +kernel

theorem checked_type5_118 : checkTypes tree [3,5,7,7,7]=true := by decide +kernel

theorem checked_type5_119 : checkTypes tree [4,4,4,4,4]=true := by decide +kernel

theorem checked_type5_120_chunk0 : checkCasesChunk tree [4,4,4,4,5] 0 64=true := by decide +kernel

theorem checked_type5_120_chunk64 : checkCasesChunk tree [4,4,4,4,5] 64 16=true := by decide +kernel

theorem checked_type5_121 : checkTypes tree [4,4,4,4,7]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_121


