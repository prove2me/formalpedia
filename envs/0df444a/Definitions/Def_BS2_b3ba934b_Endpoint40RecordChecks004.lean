-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks004
-- name    : BS2_b3ba934b_Endpoint40RecordChecks004
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:20:29.700542+00:00
-- url     : https://prove2.me/theorems/1b541813-1977-4c11-b132-b05ed9ccf6f7
-- title:
--   Sensitivity separation: Endpoint40RecordChecks004 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks004` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks004.lean; original SHA-256 d16827db64de5cb351717a7251a69597545f84364c4f4837b4c39951a85a3bfb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_48 : checkTypes tree [1,2,2,5]=true := by decide +kernel

theorem checked_type4_49 : checkTypes tree [1,2,2,6]=true := by decide +kernel

theorem checked_type4_50 : checkTypes tree [1,2,2,7]=true := by decide +kernel

theorem checked_type4_51 : checkTypes tree [1,2,3,4]=true := by decide +kernel

theorem checked_type4_52 : checkTypes tree [1,2,3,5]=true := by decide +kernel

theorem checked_type4_53 : checkTypes tree [1,2,3,7]=true := by decide +kernel

theorem checked_type4_54 : checkTypes tree [1,2,4,4]=true := by decide +kernel

theorem checked_type4_55 : checkTypes tree [1,2,4,5]=true := by decide +kernel

theorem checked_type4_56 : checkTypes tree [1,2,4,6]=true := by decide +kernel

theorem checked_type4_57 : checkTypes tree [1,2,4,7]=true := by decide +kernel

theorem checked_type4_58 : checkTypes tree [1,2,5,5]=true := by decide +kernel

theorem checked_type4_59 : checkTypes tree [1,2,5,6]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_59


