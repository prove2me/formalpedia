-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchProgram
-- name    : Submission_ThreeSum_LightBlockSourceBatchProgram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:43:34.124011+00:00
-- url     : https://prove2.me/theorems/147006fe-5bbc-4a20-8905-2f5f0b604c8f
-- title:
--   Light Block Source Batch Program
-- statement:
--   Definitions and structural lemmas for Light Block Source Batch Program, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBatchProgram.lean

import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatch
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedProgram
set_option autoImplicit false
namespace ThreeSum.LightBlockSourceBatchProgram
open Light SubsetAddress
set_option maxHeartbeats 1800000
set_option maxRecDepth 14000
def program : Program := LightBlockSourceRetainedProgram.program ++
  [LightBlockSourceBatchStep.body 0,LightBlockSourceBatch.body 41]
def sourceProcs : LightBlockSourceRetainedHost.Procs program 0 :=
  ⟨1,2,3,4,5,22,rfl,rfl,rfl,rfl,
    ⟨6,12,⟨7,8,9,10,11,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,⟨14,15,16,17,rfl,rfl,rfl,⟨18,19,20,21,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩,
    ⟨23,24,25,rfl,rfl,
      ⟨26,27,28,40,29,30,31,32,33,34,35,36,37,38,39,
        rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩,rfl⟩
def programProcs : LightBlockSourceBatch.Procs program 42 :=
  ⟨41,⟨0,sourceProcs,rfl⟩,rfl⟩
end ThreeSum.LightBlockSourceBatchProgram


