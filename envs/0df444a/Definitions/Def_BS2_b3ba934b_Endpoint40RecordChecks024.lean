-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks024
-- name    : BS2_b3ba934b_Endpoint40RecordChecks024
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:02:47.566996+00:00
-- url     : https://prove2.me/theorems/8897248d-6819-457f-b6b0-beda14aa78dc
-- title:
--   Sensitivity separation: Endpoint40RecordChecks024 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks024` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks024.lean; original SHA-256 7323c9addc9b42a37dc6fc73cbdf8c6fe897b16449a863564425519fc19322ce; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_71_chunk0 : checkCasesChunk tree [2,2,5,7,7] 0 64=true := by decide +kernel

theorem checked_type5_71_chunk64 : checkCasesChunk tree [2,2,5,7,7] 64 16=true := by decide +kernel

theorem checked_type5_72 : checkTypes tree [2,2,7,7,7]=true := by decide +kernel

theorem checked_type5_73 : checkTypes tree [2,3,3,5,5]=true := by decide +kernel

theorem checked_type5_74 : checkTypes tree [2,3,4,4,5]=true := by decide +kernel

theorem checked_type5_75 : checkTypes tree [2,3,4,5,5]=true := by decide +kernel

theorem checked_type5_76 : checkTypes tree [2,3,4,5,7]=true := by decide +kernel

theorem checked_type5_77_chunk0 : checkCasesChunk tree [2,3,5,5,5] 0 64=true := by decide +kernel

theorem checked_type5_77_chunk64 : checkCasesChunk tree [2,3,5,5,5] 64 42=true := by decide +kernel

theorem checked_type5_78 : checkTypes tree [2,3,5,5,6]=true := by decide +kernel

theorem checked_type5_79 : checkTypes tree [2,3,5,5,7]=true := by decide +kernel

theorem checked_type5_80 : checkTypes tree [2,3,5,7,7]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_80


