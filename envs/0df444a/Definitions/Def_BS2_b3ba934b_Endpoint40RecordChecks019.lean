-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks019
-- name    : BS2_b3ba934b_Endpoint40RecordChecks019
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:54:14.474027+00:00
-- url     : https://prove2.me/theorems/5a8a0df5-4ec0-4f72-bc23-ea752f3ede95
-- title:
--   Sensitivity separation: Endpoint40RecordChecks019 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks019` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks019.lean; original SHA-256 568a7f4210994b8a002c2d51fa129fb82308b8ec24cdba4983f10fbd9931eb6a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_30 : checkTypes tree [1,3,5,5,5]=true := by decide +kernel

theorem checked_type5_31 : checkTypes tree [1,3,5,5,7]=true := by decide +kernel

theorem checked_type5_32 : checkTypes tree [1,4,4,4,5]=true := by decide +kernel

theorem checked_type5_33 : checkTypes tree [1,4,4,5,5]=true := by decide +kernel

theorem checked_type5_34 : checkTypes tree [1,4,4,5,7]=true := by decide +kernel

theorem checked_type5_35_chunk0 : checkCasesChunk tree [1,4,5,5,5] 0 64=true := by decide +kernel

theorem checked_type5_35_chunk64 : checkCasesChunk tree [1,4,5,5,5] 64 42=true := by decide +kernel

theorem checked_type5_36 : checkTypes tree [1,4,5,5,6]=true := by decide +kernel

theorem checked_type5_37 : checkTypes tree [1,4,5,5,7]=true := by decide +kernel

theorem checked_type5_38 : checkTypes tree [1,4,5,7,7]=true := by decide +kernel

theorem checked_type5_39_chunk0 : checkCasesChunk tree [1,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type5_39_chunk64 : checkCasesChunk tree [1,5,5,5,5] 64 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_39_chunk64


