-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks013
-- name    : BS2_b3ba934b_Endpoint40RecordChecks013
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:25:10.760934+00:00
-- url     : https://prove2.me/theorems/788db309-f892-42ef-b889-68e081f19a2f
-- title:
--   Sensitivity separation: Endpoint40RecordChecks013 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks013` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks013.lean; original SHA-256 a05e5c55c3cb6f320c00cb6870f75340d55ef5c5a87d717e83a2f9c821ff64a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_156 : checkTypes tree [3,4,7,7]=true := by decide +kernel

theorem checked_type4_157 : checkTypes tree [3,5,5,5]=true := by decide +kernel

theorem checked_type4_158 : checkTypes tree [3,5,5,6]=true := by decide +kernel

theorem checked_type4_159 : checkTypes tree [3,5,5,7]=true := by decide +kernel

theorem checked_type4_160 : checkTypes tree [3,5,6,6]=true := by decide +kernel

theorem checked_type4_161 : checkTypes tree [3,5,6,7]=true := by decide +kernel

theorem checked_type4_162 : checkTypes tree [3,5,7,7]=true := by decide +kernel

theorem checked_type4_163 : checkTypes tree [3,6,7,7]=true := by decide +kernel

theorem checked_type4_164 : checkTypes tree [3,7,7,7]=true := by decide +kernel

theorem checked_type4_165 : checkTypes tree [4,4,4,4]=true := by decide +kernel

theorem checked_type4_166 : checkTypes tree [4,4,4,5]=true := by decide +kernel

theorem checked_type4_167 : checkTypes tree [4,4,4,6]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_167


