-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks060
-- name    : BS2_b3ba934b_Endpoint40RecordChecks060
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:56:30.591686+00:00
-- url     : https://prove2.me/theorems/b1f86084-6243-461d-abac-2466b95888af
-- title:
--   Sensitivity separation: Endpoint40RecordChecks060 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks060` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks060.lean; original SHA-256 3273da7321b6e5a43202c13731f70b8e4f808f71eb241882e8a1192fa622916c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_28_chunk192 : checkCasesChunk tree [5,5,5,5,5,6] 192 64=true := by decide +kernel

theorem checked_type6_28_chunk256 : checkCasesChunk tree [5,5,5,5,5,6] 256 64=true := by decide +kernel

theorem checked_type6_28_chunk320 : checkCasesChunk tree [5,5,5,5,5,6] 320 64=true := by decide +kernel

theorem checked_type6_28_chunk384 : checkCasesChunk tree [5,5,5,5,5,6] 384 40=true := by decide +kernel

theorem checked_type6_29_chunk0 : checkCasesChunk tree [5,5,5,5,5,7] 0 64=true := by decide +kernel

theorem checked_type6_29_chunk64 : checkCasesChunk tree [5,5,5,5,5,7] 64 64=true := by decide +kernel

theorem checked_type6_29_chunk128 : checkCasesChunk tree [5,5,5,5,5,7] 128 64=true := by decide +kernel

theorem checked_type6_29_chunk192 : checkCasesChunk tree [5,5,5,5,5,7] 192 64=true := by decide +kernel

theorem checked_type6_29_chunk256 : checkCasesChunk tree [5,5,5,5,5,7] 256 64=true := by decide +kernel

theorem checked_type6_29_chunk320 : checkCasesChunk tree [5,5,5,5,5,7] 320 64=true := by decide +kernel

theorem checked_type6_29_chunk384 : checkCasesChunk tree [5,5,5,5,5,7] 384 64=true := by decide +kernel

theorem checked_type6_29_chunk448 : checkCasesChunk tree [5,5,5,5,5,7] 448 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_29_chunk448


