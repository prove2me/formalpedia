-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks034
-- name    : BS2_b3ba934b_Endpoint40RecordChecks034
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:08:24.992633+00:00
-- url     : https://prove2.me/theorems/a1c681f6-1391-4ac1-9249-cc7a6aecd1fa
-- title:
--   Sensitivity separation: Endpoint40RecordChecks034 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks034` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks034.lean; original SHA-256 ab26f7d23e97e14a8a719d6b3b55cc8a7cdad39571ba0fc41fe7df8a956b8f48; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_136 : checkTypes tree [4,5,5,6,7]=true := by decide +kernel

theorem checked_type5_137_chunk0 : checkCasesChunk tree [4,5,5,7,7] 0 64=true := by decide +kernel

theorem checked_type5_137_chunk64 : checkCasesChunk tree [4,5,5,7,7] 64 64=true := by decide +kernel

theorem checked_type5_137_chunk128 : checkCasesChunk tree [4,5,5,7,7] 128 44=true := by decide +kernel

theorem checked_type5_138 : checkTypes tree [4,5,6,7,7]=true := by decide +kernel

theorem checked_type5_139_chunk0 : checkCasesChunk tree [4,5,7,7,7] 0 64=true := by decide +kernel

theorem checked_type5_139_chunk64 : checkCasesChunk tree [4,5,7,7,7] 64 16=true := by decide +kernel

theorem checked_type5_140 : checkTypes tree [4,7,7,7,7]=true := by decide +kernel

theorem checked_type5_141_chunk0 : checkCasesChunk tree [5,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type5_141_chunk64 : checkCasesChunk tree [5,5,5,5,5] 64 64=true := by decide +kernel

theorem checked_type5_141_chunk128 : checkCasesChunk tree [5,5,5,5,5] 128 64=true := by decide +kernel

theorem checked_type5_141_chunk192 : checkCasesChunk tree [5,5,5,5,5] 192 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_141_chunk192


