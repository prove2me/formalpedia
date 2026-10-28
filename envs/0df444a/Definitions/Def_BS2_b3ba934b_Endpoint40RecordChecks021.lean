-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks021
-- name    : BS2_b3ba934b_Endpoint40RecordChecks021
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:59:50.748682+00:00
-- url     : https://prove2.me/theorems/6352c1be-3cbd-4441-9a96-d2606efb109f
-- title:
--   Sensitivity separation: Endpoint40RecordChecks021 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks021` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks021.lean; original SHA-256 a4c6f49de3e9dcb5a2a148f6315d5a86ff4989b1a9cf77ff48d116758e47a811; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_49 : checkTypes tree [2,2,2,3,5]=true := by decide +kernel

theorem checked_type5_50 : checkTypes tree [2,2,2,4,4]=true := by decide +kernel

theorem checked_type5_51_chunk0 : checkCasesChunk tree [2,2,2,4,5] 0 64=true := by decide +kernel

theorem checked_type5_51_chunk64 : checkCasesChunk tree [2,2,2,4,5] 64 16=true := by decide +kernel

theorem checked_type5_52 : checkTypes tree [2,2,2,4,7]=true := by decide +kernel

theorem checked_type5_53_chunk0 : checkCasesChunk tree [2,2,2,5,5] 0 64=true := by decide +kernel

theorem checked_type5_53_chunk64 : checkCasesChunk tree [2,2,2,5,5] 64 64=true := by decide +kernel

theorem checked_type5_53_chunk128 : checkCasesChunk tree [2,2,2,5,5] 128 44=true := by decide +kernel

theorem checked_type5_54 : checkTypes tree [2,2,2,5,6]=true := by decide +kernel

theorem checked_type5_55_chunk0 : checkCasesChunk tree [2,2,2,5,7] 0 64=true := by decide +kernel

theorem checked_type5_55_chunk64 : checkCasesChunk tree [2,2,2,5,7] 64 16=true := by decide +kernel

theorem checked_type5_56 : checkTypes tree [2,2,2,7,7]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_56


