-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks037
-- name    : BS2_b3ba934b_Endpoint40RecordChecks037
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:09:37.511924+00:00
-- url     : https://prove2.me/theorems/956fbad6-cfdb-49ee-8b0a-d67a70d5a977
-- title:
--   Sensitivity separation: Endpoint40RecordChecks037 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks037` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks037.lean; original SHA-256 89df839c71b21b0380d88584df0a9cf167fa03529898e2e470242a565878444d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_146_chunk192 : checkCasesChunk tree [5,5,5,7,7] 192 64=true := by decide +kernel

theorem checked_type5_146_chunk256 : checkCasesChunk tree [5,5,5,7,7] 256 48=true := by decide +kernel

theorem checked_type5_147 : checkTypes tree [5,5,6,6,7]=true := by decide +kernel

theorem checked_type5_148 : checkTypes tree [5,5,6,7,7]=true := by decide +kernel

theorem checked_type5_149_chunk0 : checkCasesChunk tree [5,5,7,7,7] 0 64=true := by decide +kernel

theorem checked_type5_149_chunk64 : checkCasesChunk tree [5,5,7,7,7] 64 64=true := by decide +kernel

theorem checked_type5_149_chunk128 : checkCasesChunk tree [5,5,7,7,7] 128 44=true := by decide +kernel

theorem checked_type5_150 : checkTypes tree [5,6,7,7,7]=true := by decide +kernel

theorem checked_type5_151_chunk0 : checkCasesChunk tree [5,7,7,7,7] 0 64=true := by decide +kernel

theorem checked_type5_151_chunk64 : checkCasesChunk tree [5,7,7,7,7] 64 16=true := by decide +kernel

theorem checked_type5_152 : checkTypes tree [7,7,7,7,7]=true := by decide +kernel

theorem checked_type6_0 : checkTypes tree [0,5,5,5,5,5]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_0


