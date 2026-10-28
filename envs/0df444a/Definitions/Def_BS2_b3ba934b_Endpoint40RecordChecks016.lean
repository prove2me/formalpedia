-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks016
-- name    : BS2_b3ba934b_Endpoint40RecordChecks016
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:26:21.795114+00:00
-- url     : https://prove2.me/theorems/ca0b4dda-3026-4a72-9576-2fd6b3559642
-- title:
--   Sensitivity separation: Endpoint40RecordChecks016 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks016` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks016.lean; original SHA-256 f81cf451701f8038f9dff971cf118b6fb9bc658cd290aa667e1862d353a05d4b; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_192 : checkTypes tree [5,6,7,7]=true := by decide +kernel

theorem checked_type4_193 : checkTypes tree [5,7,7,7]=true := by decide +kernel

theorem checked_type4_194 : checkTypes tree [6,6,7,7]=true := by decide +kernel

theorem checked_type4_195 : checkTypes tree [6,7,7,7]=true := by decide +kernel

theorem checked_type4_196 : checkTypes tree [7,7,7,7]=true := by decide +kernel

theorem checked_type5_0 : checkTypes tree [0,1,5,5,5]=true := by decide +kernel

theorem checked_type5_1 : checkTypes tree [0,2,2,5,5]=true := by decide +kernel

theorem checked_type5_2 : checkTypes tree [0,2,4,5,5]=true := by decide +kernel

theorem checked_type5_3 : checkTypes tree [0,2,5,5,5]=true := by decide +kernel

theorem checked_type5_4 : checkTypes tree [0,2,5,5,7]=true := by decide +kernel

theorem checked_type5_5 : checkTypes tree [0,3,5,5,5]=true := by decide +kernel

theorem checked_type5_6 : checkTypes tree [0,4,4,5,5]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_6


