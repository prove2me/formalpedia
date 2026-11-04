-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
-- name    : Submission_ThreeSum_LightSourceControlsHostProgram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:43:41.973775+00:00
-- url     : https://prove2.me/theorems/8fe94248-8577-49d4-a7f4-b4a3cb760af8
-- title:
--   Light Source Controls Host Program
-- statement:
--   Definitions and structural lemmas for Light Source Controls Host Program, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceControlsHostProgram.lean

import Definitions.Def_Submission_ThreeSum_LightSourceControlsHost
set_option autoImplicit false
namespace ThreeSum.LightSourceControlsHostProgram
open Light
def program : Program := LightSourceBandHostProgram.program ++
  [LightDownsetSize.body 66 73,LightSubsetSetup.body 67 71 72,
    LightPascal.buildBody 68 69,fillBody,LightPascal.rowBody 70,LightArray.linearBody,
    powTableBody,LightSubsetAddress.rankBody 72,LightSubsetOffset.body,
    LightNatPower.body,log2Body,LightSourceControlsMax.body,
    LightSourceControlsSpan.body 76,LightSourceControls.body 74 65 75 77,
    LightSourceControlsHost.body 78 64]
def retainedProcs : LightBlockSourceRetainedHost.Procs program 0 :=
  ⟨1,2,3,4,5,22,rfl,rfl,rfl,rfl,
    ⟨6,12,⟨7,8,9,10,11,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,⟨14,15,16,17,rfl,rfl,rfl,⟨18,19,20,21,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩,
    ⟨23,24,25,rfl,rfl,
      ⟨26,27,28,40,29,30,31,32,33,34,35,36,37,38,39,
        rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩,rfl⟩
def batchProcs : LightBlockSourceBatch.Procs program 42 := ⟨41,⟨0,retainedProcs,rfl⟩,rfl⟩
def banksProcs : LightSourceBandBanks.Procs program 49 :=
  ⟨46,47,48,45,rfl,rfl,rfl,⟨44,⟨43,42,rfl,batchProcs,rfl⟩,rfl⟩,rfl⟩
def originalProcs : LightSourceBucketOriginal.Procs program 50 :=
  ⟨51,56,⟨52,53,54,55,rfl,rfl,rfl,rfl,rfl⟩,⟨57,58,rfl,rfl,rfl⟩,rfl⟩
def setupProcs : LightSourceBandSetup.Procs program 62 :=
  ⟨61,60,rfl,⟨59,⟨50,originalProcs,rfl⟩,rfl⟩,rfl⟩
def pairProcs : LightSourceBandPair.Procs program 63 := ⟨62,55,setupProcs,rfl,rfl⟩
def sourceProcs : LightSourceBandHost.Procs program 64 := ⟨63,49,pairProcs,banksProcs,rfl⟩
def controlProcs : LightSourceControls.Procs program 78 :=
  ⟨74,65,75,77,76,66,67,68,69,70,71,72,73,rfl,rfl,
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩
def programProcs : LightSourceControlsHost.Procs program 79 := ⟨78,64,controlProcs,sourceProcs,rfl⟩
end ThreeSum.LightSourceControlsHostProgram


