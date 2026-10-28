-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks032
-- name    : BS2_b3ba934b_Endpoint40RecordChecks032
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:08:31.804243+00:00
-- url     : https://prove2.me/theorems/13aaa608-4070-4ab1-bb4e-deb0fc8f3c1f
-- title:
--   Sensitivity separation: Endpoint40RecordChecks032 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks032` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks032.lean; original SHA-256 78e7d34a038e83e478891734ec975a63b3eb68d3303209a4e8b1ff6a49efe09d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_127 : checkTypes tree [4,4,5,5,6]=true := by decide +kernel

theorem checked_type5_128_chunk0 : checkCasesChunk tree [4,4,5,5,7] 0 64=true := by decide +kernel

theorem checked_type5_128_chunk64 : checkCasesChunk tree [4,4,5,5,7] 64 64=true := by decide +kernel

theorem checked_type5_128_chunk128 : checkCasesChunk tree [4,4,5,5,7] 128 44=true := by decide +kernel

theorem checked_type5_129 : checkTypes tree [4,4,5,6,7]=true := by decide +kernel

theorem checked_type5_130_chunk0 : checkCasesChunk tree [4,4,5,7,7] 0 64=true := by decide +kernel

theorem checked_type5_130_chunk64 : checkCasesChunk tree [4,4,5,7,7] 64 16=true := by decide +kernel

theorem checked_type5_131 : checkTypes tree [4,4,7,7,7]=true := by decide +kernel

theorem checked_type5_132_chunk0 : checkCasesChunk tree [4,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type5_132_chunk64 : checkCasesChunk tree [4,5,5,5,5] 64 64=true := by decide +kernel

theorem checked_type5_132_chunk128 : checkCasesChunk tree [4,5,5,5,5] 128 64=true := by decide +kernel

theorem checked_type5_132_chunk192 : checkCasesChunk tree [4,5,5,5,5] 192 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_132_chunk192


