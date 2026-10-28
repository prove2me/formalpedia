-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks064
-- name    : BS2_b3ba934b_Endpoint40RecordChecks064
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:18:00.704029+00:00
-- url     : https://prove2.me/theorems/247880d2-2f27-43e7-81fb-5ccebec5c25e
-- title:
--   Sensitivity separation: Endpoint40RecordChecks064 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks064` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks064.lean; original SHA-256 af4888cab7be3d17744ecadcb96b5a6470afbe5f9abba574ec7513eae24d45f0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RegularRecord
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_31_chunk512 : checkCasesChunk tree [5,5,5,5,7,7] 512 64=true := by decide +kernel

theorem checked_type6_31_chunk576 : checkCasesChunk tree [5,5,5,5,7,7] 576 64=true := by decide +kernel

theorem checked_type6_31_chunk640 : checkCasesChunk tree [5,5,5,5,7,7] 640 48=true := by decide +kernel

theorem checked_type6_32_chunk0 : checkCasesChunk tree [5,5,5,7,7,7] 0 64=true := by decide +kernel

theorem checked_type6_32_chunk64 : checkCasesChunk tree [5,5,5,7,7,7] 64 64=true := by decide +kernel

theorem checked_type6_32_chunk128 : checkCasesChunk tree [5,5,5,7,7,7] 128 4=true := by decide +kernel

theorem checked_type7_0_chunk0 : checkCasesChunk tree [5,5,5,5,5,5,5] 0 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 0 64

theorem checked_type7_0_chunk64 : checkCasesChunk tree [5,5,5,5,5,5,5] 64 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 64 64

theorem checked_type7_0_chunk128 : checkCasesChunk tree [5,5,5,5,5,5,5] 128 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 128 64

theorem checked_type7_0_chunk192 : checkCasesChunk tree [5,5,5,5,5,5,5] 192 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 192 64

theorem checked_type7_0_chunk256 : checkCasesChunk tree [5,5,5,5,5,5,5] 256 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 256 64

theorem checked_type7_0_chunk320 : checkCasesChunk tree [5,5,5,5,5,5,5] 320 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 320 64

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type7_0_chunk320


