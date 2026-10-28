-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks000
-- name    : BS2_b3ba934b_Endpoint40RecordChecks000
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:18:14.047601+00:00
-- url     : https://prove2.me/theorems/71be0749-3805-486f-8228-39c2cc8401f3
-- title:
--   Sensitivity separation: Endpoint40RecordChecks000 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks000` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks000.lean; original SHA-256 3da86f60c19a3344e16b49e52b571f01d6e08c93e7ea26aa34cafce699a5e8f9; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_0 : checkTypes tree [0,1,2,5]=true := by decide +kernel

theorem checked_type4_1 : checkTypes tree [0,1,4,5]=true := by decide +kernel

theorem checked_type4_2 : checkTypes tree [0,1,5,5]=true := by decide +kernel

theorem checked_type4_3 : checkTypes tree [0,1,5,7]=true := by decide +kernel

theorem checked_type4_4 : checkTypes tree [0,2,2,2]=true := by decide +kernel

theorem checked_type4_5 : checkTypes tree [0,2,2,4]=true := by decide +kernel

theorem checked_type4_6 : checkTypes tree [0,2,2,5]=true := by decide +kernel

theorem checked_type4_7 : checkTypes tree [0,2,2,7]=true := by decide +kernel

theorem checked_type4_8 : checkTypes tree [0,2,3,5]=true := by decide +kernel

theorem checked_type4_9 : checkTypes tree [0,2,4,4]=true := by decide +kernel

theorem checked_type4_10 : checkTypes tree [0,2,4,5]=true := by decide +kernel

theorem checked_type4_11 : checkTypes tree [0,2,4,7]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_11


