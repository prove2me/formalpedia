-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks009
-- name    : BS2_b3ba934b_Endpoint40RecordChecks009
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:25:31.892375+00:00
-- url     : https://prove2.me/theorems/c124b141-2b96-418d-a491-e51311f8c6a4
-- title:
--   Sensitivity separation: Endpoint40RecordChecks009 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks009` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks009.lean; original SHA-256 46a961d21c4255fb2721ab43a1a3656d4a70718987135faf6fe22d34b34f97ba; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_108 : checkTypes tree [2,2,7,7]=true := by decide +kernel

theorem checked_type4_109 : checkTypes tree [2,3,3,4]=true := by decide +kernel

theorem checked_type4_110 : checkTypes tree [2,3,3,5]=true := by decide +kernel

theorem checked_type4_111 : checkTypes tree [2,3,3,7]=true := by decide +kernel

theorem checked_type4_112 : checkTypes tree [2,3,4,4]=true := by decide +kernel

theorem checked_type4_113 : checkTypes tree [2,3,4,5]=true := by decide +kernel

theorem checked_type4_114 : checkTypes tree [2,3,4,6]=true := by decide +kernel

theorem checked_type4_115 : checkTypes tree [2,3,4,7]=true := by decide +kernel

theorem checked_type4_116 : checkTypes tree [2,3,5,5]=true := by decide +kernel

theorem checked_type4_117 : checkTypes tree [2,3,5,6]=true := by decide +kernel

theorem checked_type4_118 : checkTypes tree [2,3,5,7]=true := by decide +kernel

theorem checked_type4_119 : checkTypes tree [2,3,6,7]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_119


