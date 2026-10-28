-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks026
-- name    : BS2_b3ba934b_Endpoint40RecordChecks026
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:05:01.159489+00:00
-- url     : https://prove2.me/theorems/3768e6b7-f7fa-40f3-8ae6-e980dc4a544c
-- title:
--   Sensitivity separation: Endpoint40RecordChecks026 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks026` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks026.lean; original SHA-256 25a69925699fd23eeaf844656f487f9237e3a51087791c8c114ab8f4fde91fdc; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_88_chunk64 : checkCasesChunk tree [2,4,5,5,5] 64 64=true := by decide +kernel

theorem checked_type5_88_chunk128 : checkCasesChunk tree [2,4,5,5,5] 128 64=true := by decide +kernel

theorem checked_type5_88_chunk192 : checkCasesChunk tree [2,4,5,5,5] 192 64=true := by decide +kernel

theorem checked_type5_88_chunk256 : checkCasesChunk tree [2,4,5,5,5] 256 48=true := by decide +kernel

theorem checked_type5_89 : checkTypes tree [2,4,5,5,6]=true := by decide +kernel

theorem checked_type5_90_chunk0 : checkCasesChunk tree [2,4,5,5,7] 0 64=true := by decide +kernel

theorem checked_type5_90_chunk64 : checkCasesChunk tree [2,4,5,5,7] 64 64=true := by decide +kernel

theorem checked_type5_90_chunk128 : checkCasesChunk tree [2,4,5,5,7] 128 44=true := by decide +kernel

theorem checked_type5_91 : checkTypes tree [2,4,5,6,7]=true := by decide +kernel

theorem checked_type5_92_chunk0 : checkCasesChunk tree [2,4,5,7,7] 0 64=true := by decide +kernel

theorem checked_type5_92_chunk64 : checkCasesChunk tree [2,4,5,7,7] 64 16=true := by decide +kernel

theorem checked_type5_93 : checkTypes tree [2,4,7,7,7]=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_93


