-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks014
-- name    : BS2_b3ba934b_Endpoint40RecordChecks014
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:25:52.068794+00:00
-- url     : https://prove2.me/theorems/8b2279a4-4389-45f7-88d0-e72725e4043d
-- title:
--   Sensitivity separation: Endpoint40RecordChecks014 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks014` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks014.lean; original SHA-256 a7745112acf6a15f029213cdf64f913c7b356990ac5a290ba23e6d4a71a9d3c8; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_168 : checkTypes tree [4,4,4,7]=true := by decide +kernel

theorem checked_type4_169 : checkTypes tree [4,4,5,5]=true := by decide +kernel

theorem checked_type4_170 : checkTypes tree [4,4,5,6]=true := by decide +kernel

theorem checked_type4_171 : checkTypes tree [4,4,5,7]=true := by decide +kernel

theorem checked_type4_172 : checkTypes tree [4,4,6,6]=true := by decide +kernel

theorem checked_type4_173 : checkTypes tree [4,4,6,7]=true := by decide +kernel

theorem checked_type4_174 : checkTypes tree [4,4,7,7]=true := by decide +kernel

theorem checked_type4_175 : checkTypes tree [4,5,5,5]=true := by decide +kernel

theorem checked_type4_176 : checkTypes tree [4,5,5,6]=true := by decide +kernel

theorem checked_type4_177 : checkTypes tree [4,5,5,7]=true := by decide +kernel

theorem checked_type4_178 : checkTypes tree [4,5,6,6]=true := by decide +kernel

theorem checked_type4_179 : checkTypes tree [4,5,6,7]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_179


