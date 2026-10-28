-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks027
-- name    : BS2_b3ba934b_Endpoint40RecordChecks027
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:05:28.270986+00:00
-- url     : https://prove2.me/theorems/3837ac39-0161-4d1e-b404-29b82c4940ce
-- title:
--   Sensitivity separation: Endpoint40RecordChecks027 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RecordChecks027` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordChecks027.lean; original SHA-256 fc61071c68c2b9d0e509c5e8fe4965439e3b4110dbabf476ac41fe9367c2ecad; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint40Records
open ThreeBoundRecordLookup

theorem checked_type5_94_chunk0 : checkCasesChunk tree [2,5,5,5,5] 0 64=true := by decide +kernel

theorem checked_type5_94_chunk64 : checkCasesChunk tree [2,5,5,5,5] 64 64=true := by decide +kernel

theorem checked_type5_94_chunk128 : checkCasesChunk tree [2,5,5,5,5] 128 64=true := by decide +kernel

theorem checked_type5_94_chunk192 : checkCasesChunk tree [2,5,5,5,5] 192 64=true := by decide +kernel

theorem checked_type5_94_chunk256 : checkCasesChunk tree [2,5,5,5,5] 256 64=true := by decide +kernel

theorem checked_type5_94_chunk320 : checkCasesChunk tree [2,5,5,5,5] 320 64=true := by decide +kernel

theorem checked_type5_94_chunk384 : checkCasesChunk tree [2,5,5,5,5] 384 64=true := by decide +kernel

theorem checked_type5_94_chunk448 : checkCasesChunk tree [2,5,5,5,5] 448 32=true := by decide +kernel

theorem checked_type5_95_chunk0 : checkCasesChunk tree [2,5,5,5,6] 0 64=true := by decide +kernel

theorem checked_type5_95_chunk64 : checkCasesChunk tree [2,5,5,5,6] 64 42=true := by decide +kernel

theorem checked_type5_96_chunk0 : checkCasesChunk tree [2,5,5,5,7] 0 64=true := by decide +kernel

theorem checked_type5_96_chunk64 : checkCasesChunk tree [2,5,5,5,7] 64 64=true := by decide +kernel

end ThreeBoundEndpoint40Records

#print axioms ThreeBoundEndpoint40Records.checked_type5_96_chunk64


