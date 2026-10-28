-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks023
-- name    : BS2_b3ba934b_Endpoint40RecordChecks023
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:01:03.077152+00:00
-- url     : https://prove2.me/theorems/b96b63be-2afe-4ba6-b9b5-2a12f4ea5075
-- title:
--   Sensitivity separation: Endpoint40RecordChecks023 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks023` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks023.lean; original SHA-256 f6dcbb906b15e26c42e93367e27327e4468a3691a8567e26e429180ebc10b1a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_65_chunk64 : checkCasesChunk tree [2,2,4,5,7] 64 16=true := by decide +kernel

theorem checked_type5_66 : checkTypes tree [2,2,4,7,7]=true := by decide +kernel

theorem checked_type5_67_chunk0 : checkCasesChunk tree [2,2,5,5,5] 0 64=true := by decide +kernel

theorem checked_type5_67_chunk64 : checkCasesChunk tree [2,2,5,5,5] 64 64=true := by decide +kernel

theorem checked_type5_67_chunk128 : checkCasesChunk tree [2,2,5,5,5] 128 64=true := by decide +kernel

theorem checked_type5_67_chunk192 : checkCasesChunk tree [2,2,5,5,5] 192 64=true := by decide +kernel

theorem checked_type5_67_chunk256 : checkCasesChunk tree [2,2,5,5,5] 256 48=true := by decide +kernel

theorem checked_type5_68 : checkTypes tree [2,2,5,5,6]=true := by decide +kernel

theorem checked_type5_69_chunk0 : checkCasesChunk tree [2,2,5,5,7] 0 64=true := by decide +kernel

theorem checked_type5_69_chunk64 : checkCasesChunk tree [2,2,5,5,7] 64 64=true := by decide +kernel

theorem checked_type5_69_chunk128 : checkCasesChunk tree [2,2,5,5,7] 128 44=true := by decide +kernel

theorem checked_type5_70 : checkTypes tree [2,2,5,6,7]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_70


