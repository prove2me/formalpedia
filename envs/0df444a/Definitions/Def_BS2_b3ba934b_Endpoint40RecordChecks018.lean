-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks018
-- name    : BS2_b3ba934b_Endpoint40RecordChecks018
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:53:59.691318+00:00
-- url     : https://prove2.me/theorems/f6b95dd3-98e2-4ee0-a412-87808381c93d
-- title:
--   Sensitivity separation: Endpoint40RecordChecks018 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks018` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks018.lean; original SHA-256 3e4364544df618c519a4735850945dfcfa7f6c90aecc574ddef12143b9fc3ce7; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_19 : checkTypes tree [1,2,2,5,5]=true := by decide +kernel

theorem checked_type5_20 : checkTypes tree [1,2,2,5,7]=true := by decide +kernel

theorem checked_type5_21 : checkTypes tree [1,2,3,5,5]=true := by decide +kernel

theorem checked_type5_22 : checkTypes tree [1,2,4,4,5]=true := by decide +kernel

theorem checked_type5_23 : checkTypes tree [1,2,4,5,5]=true := by decide +kernel

theorem checked_type5_24 : checkTypes tree [1,2,4,5,7]=true := by decide +kernel

theorem checked_type5_25_chunk0 : checkCasesChunk tree [1,2,5,5,5] 0 64=true := by decide +kernel

theorem checked_type5_25_chunk64 : checkCasesChunk tree [1,2,5,5,5] 64 42=true := by decide +kernel

theorem checked_type5_26 : checkTypes tree [1,2,5,5,6]=true := by decide +kernel

theorem checked_type5_27 : checkTypes tree [1,2,5,5,7]=true := by decide +kernel

theorem checked_type5_28 : checkTypes tree [1,2,5,7,7]=true := by decide +kernel

theorem checked_type5_29 : checkTypes tree [1,3,4,5,5]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_29


