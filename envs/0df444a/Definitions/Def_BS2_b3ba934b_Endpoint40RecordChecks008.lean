-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks008
-- name    : BS2_b3ba934b_Endpoint40RecordChecks008
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:22:58.687507+00:00
-- url     : https://prove2.me/theorems/67c6673d-abde-4108-a347-b29c92ddde4a
-- title:
--   Sensitivity separation: Endpoint40RecordChecks008 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks008` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks008.lean; original SHA-256 25de041223ade70c11ac006480f4bfd98ece2abf178770a1659cc67113809ddb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_96 : checkTypes tree [2,2,3,5]=true := by decide +kernel

theorem checked_type4_97 : checkTypes tree [2,2,3,6]=true := by decide +kernel

theorem checked_type4_98 : checkTypes tree [2,2,3,7]=true := by decide +kernel

theorem checked_type4_99 : checkTypes tree [2,2,4,4]=true := by decide +kernel

theorem checked_type4_100 : checkTypes tree [2,2,4,5]=true := by decide +kernel

theorem checked_type4_101 : checkTypes tree [2,2,4,6]=true := by decide +kernel

theorem checked_type4_102 : checkTypes tree [2,2,4,7]=true := by decide +kernel

theorem checked_type4_103 : checkTypes tree [2,2,5,5]=true := by decide +kernel

theorem checked_type4_104 : checkTypes tree [2,2,5,6]=true := by decide +kernel

theorem checked_type4_105 : checkTypes tree [2,2,5,7]=true := by decide +kernel

theorem checked_type4_106 : checkTypes tree [2,2,6,6]=true := by decide +kernel

theorem checked_type4_107 : checkTypes tree [2,2,6,7]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_107


