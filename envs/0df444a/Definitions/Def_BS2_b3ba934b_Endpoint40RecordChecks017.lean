-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks017
-- name    : BS2_b3ba934b_Endpoint40RecordChecks017
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:26:35.52086+00:00
-- url     : https://prove2.me/theorems/bdbda79a-470c-44a7-9521-b2a8e5b9a802
-- title:
--   Sensitivity separation: Endpoint40RecordChecks017 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks017` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks017.lean; original SHA-256 3091a559c328db30e2788c533cbbc90605a69a00dfbb11eac9020611cb91187d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_7 : checkTypes tree [0,4,5,5,5]=true := by decide +kernel

theorem checked_type5_8 : checkTypes tree [0,4,5,5,7]=true := by decide +kernel

theorem checked_type5_9 : checkTypes tree [0,5,5,5,5]=true := by decide +kernel

theorem checked_type5_10 : checkTypes tree [0,5,5,5,6]=true := by decide +kernel

theorem checked_type5_11 : checkTypes tree [0,5,5,5,7]=true := by decide +kernel

theorem checked_type5_12 : checkTypes tree [0,5,5,7,7]=true := by decide +kernel

theorem checked_type5_13 : checkTypes tree [1,1,2,5,5]=true := by decide +kernel

theorem checked_type5_14 : checkTypes tree [1,1,4,5,5]=true := by decide +kernel

theorem checked_type5_15 : checkTypes tree [1,1,5,5,5]=true := by decide +kernel

theorem checked_type5_16 : checkTypes tree [1,1,5,5,7]=true := by decide +kernel

theorem checked_type5_17 : checkTypes tree [1,2,2,2,5]=true := by decide +kernel

theorem checked_type5_18 : checkTypes tree [1,2,2,4,5]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_18


