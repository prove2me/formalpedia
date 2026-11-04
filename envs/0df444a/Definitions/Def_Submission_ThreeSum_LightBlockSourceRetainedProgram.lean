-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedProgram
-- name    : Submission_ThreeSum_LightBlockSourceRetainedProgram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:07:28.187964+00:00
-- url     : https://prove2.me/theorems/b532148d-caa7-47ea-86e9-a117771f9daf
-- title:
--   Light Block Source Retained Program
-- statement:
--   Definitions and structural lemmas for Light Block Source Retained Program, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceRetainedProgram.lean

import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedHost
set_option autoImplicit false
namespace ThreeSum.LightBlockSourceRetainedProgram
open Light LightPascal LightSubsetAddress LightBlockSourceRetainedHost
open LocalCoverBounds SubsetAddress BlockSourceEncoding LightBlockSourceBuild
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
def program : Program :=
  [LightBlockSourceRetainedHost.body 1 5 22,
    LightDownsetEnumerationSetup.body 2 3,powTableBody,
    LightDownsetEnumeration.body 4,LightSubsetEnumeration.body 4,
    LightSourcePreparation.body 6 12,LightBlockSourceHashes.body 7 10,
    LightBlockCoefficients.body 8 9,powTableBody,LightScaleArray.body,
    LightMaskHashes.body 8 11,LightOneHot.body 11,
    LightSourceFlagArray.body 13,LightSourceMaskFlags.body 14 17,
    LightMaskBits.body 15 16,powTableBody,LightMaskErase.body 16,
    LightSourceTrim.body 18,LightSourceRowFlag.body 19 20 21,
    LightSourceRowScan.body,emodBody,LightSourceFlagTest.body,
    LightSourceRetainedStages.body 23 25,LightSourceGather.body 24,emodBody,
    LightZetaStages.body 26 27,LightDownsetSize.body 31 38,
    LightZetaPass.body 28 29,LightSubsetEnumerationSetup.body 36 40,
    LightZetaBatch.body 30,LightZetaCell.body 31 38 39 37,
    LightSubsetSetup.body 32 36 37,buildBody 33 34,fillBody,rowBody 35,
    LightArray.linearBody,powTableBody,rankBody 37,LightSubsetOffset.body,
    LightMaskErase.body 39,LightSubsetEnumeration.body 40]
def programProcs : LightBlockSourceRetainedHost.Procs program 0 :=
  ⟨1,2,3,4,5,22,rfl,rfl,rfl,rfl,
    ⟨6,12,⟨7,8,9,10,11,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,⟨14,15,16,17,rfl,rfl,rfl,⟨18,19,20,21,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩,
    ⟨23,24,25,rfl,rfl,
      ⟨26,27,28,40,29,30,31,32,33,34,35,36,37,38,39,
        rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩,rfl⟩
def factor (h J : ℕ) : ℕ :=
  1200*(J*(512*h)+1)^2+300*(J+1)*(512*h+1)+600*(J*(512*h)+1)+
  (300*(J*(512*h)+1)^2+J*(150*(512*h)+464*(Nat.log 2 ((512*h)*localPrime h+1)+1)+250)+400)+
  314*(Nat.log 2 (endpointBound h J+1)+1)+12000*(J*(512*h)+1)^4+1122
end ThreeSum.LightBlockSourceRetainedProgram


