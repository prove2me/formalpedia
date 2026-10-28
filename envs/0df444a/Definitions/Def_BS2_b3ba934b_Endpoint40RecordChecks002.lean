-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks002
-- name    : BS2_b3ba934b_Endpoint40RecordChecks002
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:18:45.568785+00:00
-- url     : https://prove2.me/theorems/faaf7e63-b3fd-40ee-86cc-6784ae8ee26b
-- title:
--   Sensitivity separation: Endpoint40RecordChecks002 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks002` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks002.lean; original SHA-256 65b6d220ff2dd08706d11b239c22f4e8d8e2b2c7e22c6290cf6392fdc5fba3f5; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_24 : checkTypes tree [0,4,5,7]=true := by decide +kernel

theorem checked_type4_25 : checkTypes tree [0,4,7,7]=true := by decide +kernel

theorem checked_type4_26 : checkTypes tree [0,5,5,5]=true := by decide +kernel

theorem checked_type4_27 : checkTypes tree [0,5,5,6]=true := by decide +kernel

theorem checked_type4_28 : checkTypes tree [0,5,5,7]=true := by decide +kernel

theorem checked_type4_29 : checkTypes tree [0,5,6,7]=true := by decide +kernel

theorem checked_type4_30 : checkTypes tree [0,5,7,7]=true := by decide +kernel

theorem checked_type4_31 : checkTypes tree [0,7,7,7]=true := by decide +kernel

theorem checked_type4_32 : checkTypes tree [1,1,1,5]=true := by decide +kernel

theorem checked_type4_33 : checkTypes tree [1,1,2,2]=true := by decide +kernel

theorem checked_type4_34 : checkTypes tree [1,1,2,4]=true := by decide +kernel

theorem checked_type4_35 : checkTypes tree [1,1,2,5]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_35


