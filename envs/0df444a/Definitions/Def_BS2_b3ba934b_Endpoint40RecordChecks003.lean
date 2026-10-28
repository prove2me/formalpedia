-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks003
-- name    : BS2_b3ba934b_Endpoint40RecordChecks003
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:19:07.207368+00:00
-- url     : https://prove2.me/theorems/3ef36198-2d06-426f-baee-01b8dc655932
-- title:
--   Sensitivity separation: Endpoint40RecordChecks003 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks003` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks003.lean; original SHA-256 9ec10c7759632ce8a20f324f7e73f93a18f7a2002c957193efc067c0ab49bc42; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_36 : checkTypes tree [1,1,2,7]=true := by decide +kernel

theorem checked_type4_37 : checkTypes tree [1,1,3,5]=true := by decide +kernel

theorem checked_type4_38 : checkTypes tree [1,1,4,4]=true := by decide +kernel

theorem checked_type4_39 : checkTypes tree [1,1,4,5]=true := by decide +kernel

theorem checked_type4_40 : checkTypes tree [1,1,4,7]=true := by decide +kernel

theorem checked_type4_41 : checkTypes tree [1,1,5,5]=true := by decide +kernel

theorem checked_type4_42 : checkTypes tree [1,1,5,6]=true := by decide +kernel

theorem checked_type4_43 : checkTypes tree [1,1,5,7]=true := by decide +kernel

theorem checked_type4_44 : checkTypes tree [1,1,7,7]=true := by decide +kernel

theorem checked_type4_45 : checkTypes tree [1,2,2,2]=true := by decide +kernel

theorem checked_type4_46 : checkTypes tree [1,2,2,3]=true := by decide +kernel

theorem checked_type4_47 : checkTypes tree [1,2,2,4]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_47


