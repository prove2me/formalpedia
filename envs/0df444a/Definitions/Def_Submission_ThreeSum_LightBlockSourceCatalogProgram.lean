-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalogProgram
-- name    : Submission_ThreeSum_LightBlockSourceCatalogProgram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:49:04.796344+00:00
-- url     : https://prove2.me/theorems/6c56732f-bbe6-40d3-b8ff-106669e9f9ed
-- title:
--   Light Block Source Catalog Program
-- statement:
--   Definitions and structural lemmas for Light Block Source Catalog Program, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceCatalogProgram.lean

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchProgram
set_option autoImplicit false
namespace ThreeSum.LightBlockSourceCatalogProgram
open Light SubsetAddress LightBlockSourceCatalog
set_option maxHeartbeats 2200000
set_option maxRecDepth 16000
def program : Program := LightBlockSourceBatchProgram.program ++
  [LightSourceOccurrenceArray.body 44,LightOutputDecodeDigits.body 45,
    LightOutputDecodeDivide.body,LightBlockSourceCatalog.body 43 42]
def sourceProcs : LightBlockSourceRetainedHost.Procs program 0 :=
  ⟨1,2,3,4,5,22,rfl,rfl,rfl,rfl,
    ⟨6,12,⟨7,8,9,10,11,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,⟨14,15,16,17,rfl,rfl,rfl,⟨18,19,20,21,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩,
    ⟨23,24,25,rfl,rfl,
      ⟨26,27,28,40,29,30,31,32,33,34,35,36,37,38,39,
        rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩,rfl⟩
def programProcs : LightBlockSourceCatalog.Procs program 46 :=
  ⟨43,44,45,42,rfl,rfl,rfl,⟨41,⟨0,sourceProcs,rfl⟩,rfl⟩,rfl⟩
def factor (h J : ℕ) : ℕ :=
  LightBlockSourceRetainedProgram.factor h J+1120+
    300*(J+1)*(Nat.log 2 (count h J+1)+2)
end ThreeSum.LightBlockSourceCatalogProgram


