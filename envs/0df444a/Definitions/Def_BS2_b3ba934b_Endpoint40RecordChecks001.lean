-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks001
-- name    : BS2_b3ba934b_Endpoint40RecordChecks001
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:18:28.161677+00:00
-- url     : https://prove2.me/theorems/6e017abd-7cbd-4a62-b0d6-1a0fed4b22a3
-- title:
--   Sensitivity separation: Endpoint40RecordChecks001 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks001` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks001.lean; original SHA-256 fd70895ae44f0f8c251a2eb1845e660b69cd9947968dfe18149a01aa7608803d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_12 : checkTypes tree [0,2,5,5]=true := by decide +kernel

theorem checked_type4_13 : checkTypes tree [0,2,5,6]=true := by decide +kernel

theorem checked_type4_14 : checkTypes tree [0,2,5,7]=true := by decide +kernel

theorem checked_type4_15 : checkTypes tree [0,2,7,7]=true := by decide +kernel

theorem checked_type4_16 : checkTypes tree [0,3,4,5]=true := by decide +kernel

theorem checked_type4_17 : checkTypes tree [0,3,5,5]=true := by decide +kernel

theorem checked_type4_18 : checkTypes tree [0,3,5,7]=true := by decide +kernel

theorem checked_type4_19 : checkTypes tree [0,4,4,4]=true := by decide +kernel

theorem checked_type4_20 : checkTypes tree [0,4,4,5]=true := by decide +kernel

theorem checked_type4_21 : checkTypes tree [0,4,4,7]=true := by decide +kernel

theorem checked_type4_22 : checkTypes tree [0,4,5,5]=true := by decide +kernel

theorem checked_type4_23 : checkTypes tree [0,4,5,6]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_23


