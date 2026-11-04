-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
-- name    : Submission_ThreeSum_LightSourceBandBanksProgram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:14:28.729675+00:00
-- url     : https://prove2.me/theorems/228c4b27-67de-4bda-ae1d-9c39eff32ae1
-- title:
--   Light Source Band Banks Program
-- statement:
--   Definitions and structural lemmas for Light Source Band Banks Program, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandBanksProgram.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanks
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchProgram
set_option autoImplicit false
namespace ThreeSum.LightSourceBandBanksProgram
open Light
def program : Program := LightBlockSourceBatchProgram.program ++
  [LightSourceBandHistSelect.body,LightSourceBandBankStep.body 43 42,
    LightSourceBandBankBatch.body 44,LightSourceOccurrenceArray.body 47,
    LightOutputDecodeDigits.body 48,LightOutputDecodeDivide.body,LightSourceBandBanks.body 46 45]
def sourceProcs : LightBlockSourceRetainedHost.Procs program 0 :=
  ⟨1,2,3,4,5,22,rfl,rfl,rfl,rfl,
    ⟨6,12,⟨7,8,9,10,11,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,⟨14,15,16,17,rfl,rfl,rfl,⟨18,19,20,21,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩,
    ⟨23,24,25,rfl,rfl,
      ⟨26,27,28,40,29,30,31,32,33,34,35,36,37,38,39,
        rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩,rfl⟩
def batchProcs : LightBlockSourceBatch.Procs program 42 :=
  ⟨41,⟨0,sourceProcs,rfl⟩,rfl⟩
def programProcs : LightSourceBandBanks.Procs program 49 :=
  ⟨46,47,48,45,rfl,rfl,rfl,⟨44,⟨43,42,rfl,batchProcs,rfl⟩,rfl⟩,rfl⟩
end ThreeSum.LightSourceBandBanksProgram


