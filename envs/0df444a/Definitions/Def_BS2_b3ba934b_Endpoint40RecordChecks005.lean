-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks005
-- name    : BS2_b3ba934b_Endpoint40RecordChecks005
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:20:51.735304+00:00
-- url     : https://prove2.me/theorems/fa29ca94-792c-4a19-99a2-10c6f00e07b5
-- title:
--   Sensitivity separation: Endpoint40RecordChecks005 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks005` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks005.lean; original SHA-256 2b39460b60e7926c76c0cd06910f0179255aca5a8fc73f8532b4a3e22b1437ad; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_60 : checkTypes tree [1,2,5,7]=true := by decide +kernel

theorem checked_type4_61 : checkTypes tree [1,2,6,7]=true := by decide +kernel

theorem checked_type4_62 : checkTypes tree [1,2,7,7]=true := by decide +kernel

theorem checked_type4_63 : checkTypes tree [1,3,3,5]=true := by decide +kernel

theorem checked_type4_64 : checkTypes tree [1,3,4,4]=true := by decide +kernel

theorem checked_type4_65 : checkTypes tree [1,3,4,5]=true := by decide +kernel

theorem checked_type4_66 : checkTypes tree [1,3,4,7]=true := by decide +kernel

theorem checked_type4_67 : checkTypes tree [1,3,5,5]=true := by decide +kernel

theorem checked_type4_68 : checkTypes tree [1,3,5,6]=true := by decide +kernel

theorem checked_type4_69 : checkTypes tree [1,3,5,7]=true := by decide +kernel

theorem checked_type4_70 : checkTypes tree [1,3,7,7]=true := by decide +kernel

theorem checked_type4_71 : checkTypes tree [1,4,4,4]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_71


