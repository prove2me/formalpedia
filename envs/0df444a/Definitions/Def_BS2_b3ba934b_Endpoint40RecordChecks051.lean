-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks051
-- name    : BS2_b3ba934b_Endpoint40RecordChecks051
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:21:43.265992+00:00
-- url     : https://prove2.me/theorems/057c0a30-cc39-4d9a-8c20-0ba406a0eb89
-- title:
--   Sensitivity separation: Endpoint40RecordChecks051 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks051` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks051.lean; original SHA-256 7ca8968f5f1634850efebf4536c0672b11c647dad4d12e0163b3ec97650dbc3f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_23_chunk1664 : checkCasesChunk tree [4,5,5,5,5,5] 1664 64=true := by decide +kernel

theorem checked_type6_23_chunk1728 : checkCasesChunk tree [4,5,5,5,5,5] 1728 64=true := by decide +kernel

theorem checked_type6_23_chunk1792 : checkCasesChunk tree [4,5,5,5,5,5] 1792 64=true := by decide +kernel

theorem checked_type6_23_chunk1856 : checkCasesChunk tree [4,5,5,5,5,5] 1856 64=true := by decide +kernel

theorem checked_type6_23_chunk1920 : checkCasesChunk tree [4,5,5,5,5,5] 1920 64=true := by decide +kernel

theorem checked_type6_23_chunk1984 : checkCasesChunk tree [4,5,5,5,5,5] 1984 64=true := by decide +kernel

theorem checked_type6_23_chunk2048 : checkCasesChunk tree [4,5,5,5,5,5] 2048 64=true := by decide +kernel

theorem checked_type6_23_chunk2112 : checkCasesChunk tree [4,5,5,5,5,5] 2112 32=true := by decide +kernel

theorem checked_type6_24_chunk0 : checkCasesChunk tree [4,5,5,5,5,6] 0 64=true := by decide +kernel

theorem checked_type6_24_chunk64 : checkCasesChunk tree [4,5,5,5,5,6] 64 16=true := by decide +kernel

theorem checked_type6_25_chunk0 : checkCasesChunk tree [4,5,5,5,5,7] 0 64=true := by decide +kernel

theorem checked_type6_25_chunk64 : checkCasesChunk tree [4,5,5,5,5,7] 64 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_25_chunk64


