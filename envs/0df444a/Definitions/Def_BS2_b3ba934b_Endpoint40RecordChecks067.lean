-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks067
-- name    : BS2_b3ba934b_Endpoint40RecordChecks067
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:27:50.621032+00:00
-- url     : https://prove2.me/theorems/13b72a13-7b33-4960-822e-3717161ace32
-- title:
--   Sensitivity separation: Endpoint40RecordChecks067 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks067` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks067.lean; original SHA-256 de7850990d02af706fb216af11b754b9d6971c8eaa776c464a95fd7b17755834; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RegularRecord
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type7_0_chunk1920 : checkCasesChunk tree [5,5,5,5,5,5,5] 1920 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 1920 64

theorem checked_type7_0_chunk1984 : checkCasesChunk tree [5,5,5,5,5,5,5] 1984 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 1984 64

theorem checked_type7_0_chunk2048 : checkCasesChunk tree [5,5,5,5,5,5,5] 2048 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 2048 64

theorem checked_type7_0_chunk2112 : checkCasesChunk tree [5,5,5,5,5,5,5] 2112 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 2112 64

theorem checked_type7_0_chunk2176 : checkCasesChunk tree [5,5,5,5,5,5,5] 2176 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 2176 64

theorem checked_type7_0_chunk2240 : checkCasesChunk tree [5,5,5,5,5,5,5] 2240 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 2240 64

theorem checked_type7_0_chunk2304 : checkCasesChunk tree [5,5,5,5,5,5,5] 2304 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 2304 64

theorem checked_type7_0_chunk2368 : checkCasesChunk tree [5,5,5,5,5,5,5] 2368 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 2368 64

theorem checked_type7_0_chunk2432 : checkCasesChunk tree [5,5,5,5,5,5,5] 2432 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 2432 64

theorem checked_type7_0_chunk2496 : checkCasesChunk tree [5,5,5,5,5,5,5] 2496 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 2496 64

theorem checked_type7_0_chunk2560 : checkCasesChunk tree [5,5,5,5,5,5,5] 2560 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 2560 64

theorem checked_type7_0_chunk2624 : checkCasesChunk tree [5,5,5,5,5,5,5] 2624 16=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 2624 16

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type7_0_chunk2624


