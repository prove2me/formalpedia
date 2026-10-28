-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks010
-- name    : BS2_b3ba934b_Endpoint40RecordChecks010
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:23:40.931598+00:00
-- url     : https://prove2.me/theorems/89080a34-4423-4049-a0f2-da86307e8972
-- title:
--   Sensitivity separation: Endpoint40RecordChecks010 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks010` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks010.lean; original SHA-256 efb9eb9691833b8944aa566490dbb30907305f0981cf0f1d5a6a99b2d66e0a3e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_120 : checkTypes tree [2,3,7,7]=true := by decide +kernel

theorem checked_type4_121 : checkTypes tree [2,4,4,4]=true := by decide +kernel

theorem checked_type4_122 : checkTypes tree [2,4,4,5]=true := by decide +kernel

theorem checked_type4_123 : checkTypes tree [2,4,4,6]=true := by decide +kernel

theorem checked_type4_124 : checkTypes tree [2,4,4,7]=true := by decide +kernel

theorem checked_type4_125 : checkTypes tree [2,4,5,5]=true := by decide +kernel

theorem checked_type4_126 : checkTypes tree [2,4,5,6]=true := by decide +kernel

theorem checked_type4_127 : checkTypes tree [2,4,5,7]=true := by decide +kernel

theorem checked_type4_128 : checkTypes tree [2,4,6,6]=true := by decide +kernel

theorem checked_type4_129 : checkTypes tree [2,4,6,7]=true := by decide +kernel

theorem checked_type4_130 : checkTypes tree [2,4,7,7]=true := by decide +kernel

theorem checked_type4_131 : checkTypes tree [2,5,5,5]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_131


