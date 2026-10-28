-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks022
-- name    : BS2_b3ba934b_Endpoint40RecordChecks022
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:01:56.424878+00:00
-- url     : https://prove2.me/theorems/593a5297-6f13-4a47-9dba-8aadedcddcc4
-- title:
--   Sensitivity separation: Endpoint40RecordChecks022 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks022` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks022.lean; original SHA-256 7009069ffab199f6718259b8057948d1e6ac666bec98ccde95d7e297732c482e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_57 : checkTypes tree [2,2,3,4,5]=true := by decide +kernel

theorem checked_type5_58 : checkTypes tree [2,2,3,5,5]=true := by decide +kernel

theorem checked_type5_59 : checkTypes tree [2,2,3,5,7]=true := by decide +kernel

theorem checked_type5_60 : checkTypes tree [2,2,4,4,4]=true := by decide +kernel

theorem checked_type5_61_chunk0 : checkCasesChunk tree [2,2,4,4,5] 0 64=true := by decide +kernel

theorem checked_type5_61_chunk64 : checkCasesChunk tree [2,2,4,4,5] 64 16=true := by decide +kernel

theorem checked_type5_62 : checkTypes tree [2,2,4,4,7]=true := by decide +kernel

theorem checked_type5_63_chunk0 : checkCasesChunk tree [2,2,4,5,5] 0 64=true := by decide +kernel

theorem checked_type5_63_chunk64 : checkCasesChunk tree [2,2,4,5,5] 64 64=true := by decide +kernel

theorem checked_type5_63_chunk128 : checkCasesChunk tree [2,2,4,5,5] 128 44=true := by decide +kernel

theorem checked_type5_64 : checkTypes tree [2,2,4,5,6]=true := by decide +kernel

theorem checked_type5_65_chunk0 : checkCasesChunk tree [2,2,4,5,7] 0 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_65_chunk0


