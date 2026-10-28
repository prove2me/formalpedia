-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks011
-- name    : BS2_b3ba934b_Endpoint40RecordChecks011
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:24:11.669125+00:00
-- url     : https://prove2.me/theorems/366f0cd9-f305-4b5e-8f74-942d9282b77e
-- title:
--   Sensitivity separation: Endpoint40RecordChecks011 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks011` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks011.lean; original SHA-256 e780a5813066a13e424a763d76232f4591df36cc3d9b8ef4b0e759e3bb401fe7; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_132 : checkTypes tree [2,5,5,6]=true := by decide +kernel

theorem checked_type4_133 : checkTypes tree [2,5,5,7]=true := by decide +kernel

theorem checked_type4_134 : checkTypes tree [2,5,6,6]=true := by decide +kernel

theorem checked_type4_135 : checkTypes tree [2,5,6,7]=true := by decide +kernel

theorem checked_type4_136 : checkTypes tree [2,5,7,7]=true := by decide +kernel

theorem checked_type4_137 : checkTypes tree [2,6,6,7]=true := by decide +kernel

theorem checked_type4_138 : checkTypes tree [2,6,7,7]=true := by decide +kernel

theorem checked_type4_139 : checkTypes tree [2,7,7,7]=true := by decide +kernel

theorem checked_type4_140 : checkTypes tree [3,3,3,5]=true := by decide +kernel

theorem checked_type4_141 : checkTypes tree [3,3,4,4]=true := by decide +kernel

theorem checked_type4_142 : checkTypes tree [3,3,4,5]=true := by decide +kernel

theorem checked_type4_143 : checkTypes tree [3,3,4,7]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_143


