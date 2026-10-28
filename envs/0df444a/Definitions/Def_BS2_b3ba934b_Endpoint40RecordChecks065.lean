-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks065
-- name    : BS2_b3ba934b_Endpoint40RecordChecks065
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:27:03.521002+00:00
-- url     : https://prove2.me/theorems/bf037401-7e3a-4fe0-990a-5c81fe0a416c
-- title:
--   Sensitivity separation: Endpoint40RecordChecks065 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks065` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks065.lean; original SHA-256 e1e98e0e1cefe8b6f26568bb77d70e4fd9c5a97a3bfafffad9caf1d76792b171; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RegularRecord
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type7_0_chunk384 : checkCasesChunk tree [5,5,5,5,5,5,5] 384 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 384 64

theorem checked_type7_0_chunk448 : checkCasesChunk tree [5,5,5,5,5,5,5] 448 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 448 64

theorem checked_type7_0_chunk512 : checkCasesChunk tree [5,5,5,5,5,5,5] 512 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 512 64

theorem checked_type7_0_chunk576 : checkCasesChunk tree [5,5,5,5,5,5,5] 576 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 576 64

theorem checked_type7_0_chunk640 : checkCasesChunk tree [5,5,5,5,5,5,5] 640 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 640 64

theorem checked_type7_0_chunk704 : checkCasesChunk tree [5,5,5,5,5,5,5] 704 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 704 64

theorem checked_type7_0_chunk768 : checkCasesChunk tree [5,5,5,5,5,5,5] 768 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 768 64

theorem checked_type7_0_chunk832 : checkCasesChunk tree [5,5,5,5,5,5,5] 832 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 832 64

theorem checked_type7_0_chunk896 : checkCasesChunk tree [5,5,5,5,5,5,5] 896 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 896 64

theorem checked_type7_0_chunk960 : checkCasesChunk tree [5,5,5,5,5,5,5] 960 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 960 64

theorem checked_type7_0_chunk1024 : checkCasesChunk tree [5,5,5,5,5,5,5] 1024 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 1024 64

theorem checked_type7_0_chunk1088 : checkCasesChunk tree [5,5,5,5,5,5,5] 1088 64=true := ThreeBoundEndpoint40Regular.checked_regular_chunk 1088 64

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type7_0_chunk1088


