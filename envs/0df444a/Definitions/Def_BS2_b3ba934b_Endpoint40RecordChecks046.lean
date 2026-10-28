-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks046
-- name    : BS2_b3ba934b_Endpoint40RecordChecks046
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:18:36.584983+00:00
-- url     : https://prove2.me/theorems/5d571f31-ad7b-4789-94b8-a988554bf4dc
-- title:
--   Sensitivity separation: Endpoint40RecordChecks046 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks046` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks046.lean; original SHA-256 7a6097e4dadbbf2b55587ab6693df2b68bdc6954950c275884ae3f6608de3baf; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_15_chunk512 : checkCasesChunk tree [2,5,5,5,5,7] 512 64=true := by decide +kernel

theorem checked_type6_15_chunk576 : checkCasesChunk tree [2,5,5,5,5,7] 576 64=true := by decide +kernel

theorem checked_type6_15_chunk640 : checkCasesChunk tree [2,5,5,5,5,7] 640 48=true := by decide +kernel

theorem checked_type6_16_chunk0 : checkCasesChunk tree [2,5,5,5,7,7] 0 64=true := by decide +kernel

theorem checked_type6_16_chunk64 : checkCasesChunk tree [2,5,5,5,7,7] 64 64=true := by decide +kernel

theorem checked_type6_16_chunk128 : checkCasesChunk tree [2,5,5,5,7,7] 128 4=true := by decide +kernel

theorem checked_type6_17_chunk0 : checkCasesChunk tree [3,4,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type6_17_chunk64 : checkCasesChunk tree [3,4,5,5,5,5] 64 16=true := by decide +kernel

theorem checked_type6_18_chunk0 : checkCasesChunk tree [3,5,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type6_18_chunk64 : checkCasesChunk tree [3,5,5,5,5,5] 64 64=true := by decide +kernel

theorem checked_type6_18_chunk128 : checkCasesChunk tree [3,5,5,5,5,5] 128 64=true := by decide +kernel

theorem checked_type6_18_chunk192 : checkCasesChunk tree [3,5,5,5,5,5] 192 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_18_chunk192


