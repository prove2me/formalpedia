-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks061
-- name    : BS2_b3ba934b_Endpoint40RecordChecks061
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:57:37.098968+00:00
-- url     : https://prove2.me/theorems/6d325997-cfe3-45e5-bf92-a70400e79713
-- title:
--   Sensitivity separation: Endpoint40RecordChecks061 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks061` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks061.lean; original SHA-256 017eae860f09cf845414c33993e577336eef73420e3217b9db15513920ac9111; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type6_29_chunk512 : checkCasesChunk tree [5,5,5,5,5,7] 512 64=true := by decide +kernel

theorem checked_type6_29_chunk576 : checkCasesChunk tree [5,5,5,5,5,7] 576 64=true := by decide +kernel

theorem checked_type6_29_chunk640 : checkCasesChunk tree [5,5,5,5,5,7] 640 64=true := by decide +kernel

theorem checked_type6_29_chunk704 : checkCasesChunk tree [5,5,5,5,5,7] 704 64=true := by decide +kernel

theorem checked_type6_29_chunk768 : checkCasesChunk tree [5,5,5,5,5,7] 768 64=true := by decide +kernel

theorem checked_type6_29_chunk832 : checkCasesChunk tree [5,5,5,5,5,7] 832 64=true := by decide +kernel

theorem checked_type6_29_chunk896 : checkCasesChunk tree [5,5,5,5,5,7] 896 64=true := by decide +kernel

theorem checked_type6_29_chunk960 : checkCasesChunk tree [5,5,5,5,5,7] 960 64=true := by decide +kernel

theorem checked_type6_29_chunk1024 : checkCasesChunk tree [5,5,5,5,5,7] 1024 64=true := by decide +kernel

theorem checked_type6_29_chunk1088 : checkCasesChunk tree [5,5,5,5,5,7] 1088 64=true := by decide +kernel

theorem checked_type6_29_chunk1152 : checkCasesChunk tree [5,5,5,5,5,7] 1152 64=true := by decide +kernel

theorem checked_type6_29_chunk1216 : checkCasesChunk tree [5,5,5,5,5,7] 1216 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type6_29_chunk1216


