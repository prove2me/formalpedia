-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks015
-- name    : BS2_b3ba934b_Endpoint40RecordChecks015
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:26:09.493091+00:00
-- url     : https://prove2.me/theorems/695479cb-43bd-4cf6-aa69-f349ff0a5458
-- title:
--   Sensitivity separation: Endpoint40RecordChecks015 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks015` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks015.lean; original SHA-256 60f4a68a35da11cc0396a9724c3512fe1d05abba96c57a4f27ae3e3b9316c867; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type4_180 : checkTypes tree [4,5,7,7]=true := by decide +kernel

theorem checked_type4_181 : checkTypes tree [4,6,6,7]=true := by decide +kernel

theorem checked_type4_182 : checkTypes tree [4,6,7,7]=true := by decide +kernel

theorem checked_type4_183 : checkTypes tree [4,7,7,7]=true := by decide +kernel

theorem checked_type4_184 : checkTypes tree [5,5,5,5]=true := by decide +kernel

theorem checked_type4_185 : checkTypes tree [5,5,5,6]=true := by decide +kernel

theorem checked_type4_186 : checkTypes tree [5,5,5,7]=true := by decide +kernel

theorem checked_type4_187 : checkTypes tree [5,5,6,6]=true := by decide +kernel

theorem checked_type4_188 : checkTypes tree [5,5,6,7]=true := by decide +kernel

theorem checked_type4_189 : checkTypes tree [5,5,7,7]=true := by decide +kernel

theorem checked_type4_190 : checkTypes tree [5,6,6,6]=true := by decide +kernel

theorem checked_type4_191 : checkTypes tree [5,6,6,7]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type4_191


