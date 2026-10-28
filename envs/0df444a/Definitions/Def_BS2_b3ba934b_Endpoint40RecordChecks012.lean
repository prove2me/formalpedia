-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks012
-- name    : BS2_b3ba934b_Endpoint40RecordChecks012
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:24:33.0882+00:00
-- url     : https://prove2.me/theorems/1dd5abfa-3a76-47cf-be2e-f698d55ebb0b
-- title:
--   Sensitivity separation: Endpoint40RecordChecks012 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks012` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks012.lean; original SHA-256 18ea3e0f4c33a0a8294597068010848c1e0624d9155e8ddec144eeb253bee368; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_144 : checkTypes tree [3,3,5,5]=true := by decide +kernel

theorem checked_type4_145 : checkTypes tree [3,3,5,6]=true := by decide +kernel

theorem checked_type4_146 : checkTypes tree [3,3,5,7]=true := by decide +kernel

theorem checked_type4_147 : checkTypes tree [3,3,7,7]=true := by decide +kernel

theorem checked_type4_148 : checkTypes tree [3,4,4,4]=true := by decide +kernel

theorem checked_type4_149 : checkTypes tree [3,4,4,5]=true := by decide +kernel

theorem checked_type4_150 : checkTypes tree [3,4,4,6]=true := by decide +kernel

theorem checked_type4_151 : checkTypes tree [3,4,4,7]=true := by decide +kernel

theorem checked_type4_152 : checkTypes tree [3,4,5,5]=true := by decide +kernel

theorem checked_type4_153 : checkTypes tree [3,4,5,6]=true := by decide +kernel

theorem checked_type4_154 : checkTypes tree [3,4,5,7]=true := by decide +kernel

theorem checked_type4_155 : checkTypes tree [3,4,6,7]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_155


