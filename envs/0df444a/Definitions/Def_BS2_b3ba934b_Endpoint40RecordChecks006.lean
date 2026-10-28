-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks006
-- name    : BS2_b3ba934b_Endpoint40RecordChecks006
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:21:52.935036+00:00
-- url     : https://prove2.me/theorems/ad3da4bb-2c1f-470f-a4dc-212b725a4470
-- title:
--   Sensitivity separation: Endpoint40RecordChecks006 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks006` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks006.lean; original SHA-256 c502382ccce2b5bb6aee54fb619a9212d0f6a798adb47590b9f9d2b3b25fd19b; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_72 : checkTypes tree [1,4,4,5]=true := by decide +kernel

theorem checked_type4_73 : checkTypes tree [1,4,4,6]=true := by decide +kernel

theorem checked_type4_74 : checkTypes tree [1,4,4,7]=true := by decide +kernel

theorem checked_type4_75 : checkTypes tree [1,4,5,5]=true := by decide +kernel

theorem checked_type4_76 : checkTypes tree [1,4,5,6]=true := by decide +kernel

theorem checked_type4_77 : checkTypes tree [1,4,5,7]=true := by decide +kernel

theorem checked_type4_78 : checkTypes tree [1,4,6,7]=true := by decide +kernel

theorem checked_type4_79 : checkTypes tree [1,4,7,7]=true := by decide +kernel

theorem checked_type4_80 : checkTypes tree [1,5,5,5]=true := by decide +kernel

theorem checked_type4_81 : checkTypes tree [1,5,5,6]=true := by decide +kernel

theorem checked_type4_82 : checkTypes tree [1,5,5,7]=true := by decide +kernel

theorem checked_type4_83 : checkTypes tree [1,5,6,6]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_83


