-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks007
-- name    : BS2_b3ba934b_Endpoint40RecordChecks007
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:22:20.627716+00:00
-- url     : https://prove2.me/theorems/b0a7b8d7-31d9-45b3-b5c2-21d1815accf4
-- title:
--   Sensitivity separation: Endpoint40RecordChecks007 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks007` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks007.lean; original SHA-256 bc4456c4d1321b51cc721f0382ff55c95824659171dcba4e49c9b290e32514e6; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_84 : checkTypes tree [1,5,6,7]=true := by decide +kernel

theorem checked_type4_85 : checkTypes tree [1,5,7,7]=true := by decide +kernel

theorem checked_type4_86 : checkTypes tree [1,6,7,7]=true := by decide +kernel

theorem checked_type4_87 : checkTypes tree [1,7,7,7]=true := by decide +kernel

theorem checked_type4_88 : checkTypes tree [2,2,2,2]=true := by decide +kernel

theorem checked_type4_89 : checkTypes tree [2,2,2,3]=true := by decide +kernel

theorem checked_type4_90 : checkTypes tree [2,2,2,4]=true := by decide +kernel

theorem checked_type4_91 : checkTypes tree [2,2,2,5]=true := by decide +kernel

theorem checked_type4_92 : checkTypes tree [2,2,2,6]=true := by decide +kernel

theorem checked_type4_93 : checkTypes tree [2,2,2,7]=true := by decide +kernel

theorem checked_type4_94 : checkTypes tree [2,2,3,3]=true := by decide +kernel

theorem checked_type4_95 : checkTypes tree [2,2,3,4]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_95


