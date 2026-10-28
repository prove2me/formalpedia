-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks033
-- name    : BS2_b3ba934b_Endpoint40RecordChecks033
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:08:15.886288+00:00
-- url     : https://prove2.me/theorems/9ab662f0-c496-4981-94de-7b71228d7004
-- title:
--   Sensitivity separation: Endpoint40RecordChecks033 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks033` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks033.lean; original SHA-256 76dac2e9c62c3a173387c268778b650954786beb7eaed8fd7a77dcdda9967751; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_132_chunk256 : checkCasesChunk tree [4,5,5,5,5] 256 64=true := by decide +kernel

theorem checked_type5_132_chunk320 : checkCasesChunk tree [4,5,5,5,5] 320 64=true := by decide +kernel

theorem checked_type5_132_chunk384 : checkCasesChunk tree [4,5,5,5,5] 384 64=true := by decide +kernel

theorem checked_type5_132_chunk448 : checkCasesChunk tree [4,5,5,5,5] 448 32=true := by decide +kernel

theorem checked_type5_133_chunk0 : checkCasesChunk tree [4,5,5,5,6] 0 64=true := by decide +kernel

theorem checked_type5_133_chunk64 : checkCasesChunk tree [4,5,5,5,6] 64 42=true := by decide +kernel

theorem checked_type5_134_chunk0 : checkCasesChunk tree [4,5,5,5,7] 0 64=true := by decide +kernel

theorem checked_type5_134_chunk64 : checkCasesChunk tree [4,5,5,5,7] 64 64=true := by decide +kernel

theorem checked_type5_134_chunk128 : checkCasesChunk tree [4,5,5,5,7] 128 64=true := by decide +kernel

theorem checked_type5_134_chunk192 : checkCasesChunk tree [4,5,5,5,7] 192 64=true := by decide +kernel

theorem checked_type5_134_chunk256 : checkCasesChunk tree [4,5,5,5,7] 256 48=true := by decide +kernel

theorem checked_type5_135 : checkTypes tree [4,5,5,6,6]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_135


