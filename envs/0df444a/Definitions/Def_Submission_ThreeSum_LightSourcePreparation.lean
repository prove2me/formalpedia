-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourcePreparation
-- name    : Submission_ThreeSum_LightSourcePreparation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:48:14.116419+00:00
-- url     : https://prove2.me/theorems/442ec0f4-b8d3-4e36-b977-a5107adb3a42
-- title:
--   Light Source Preparation
-- statement:
--   Definitions and structural lemmas for Light Source Preparation, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourcePreparation.lean

import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightSourceFlagArray
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSourcePreparation
open Light BlockCoefficientRows
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
def body (pHashes pFlags : ℕ) : Stmt :=
  .call pHashes [v 0,v 1,v 3,v 5,v 6,v 12,v 13,v 10,v 14,v 15,v 11,v 19] 20 ;;
  .call pFlags [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 16,v 17,v 18,v 19] 20
def time (n J L U : ℕ) : ℕ :=
  LightBlockSourceHashes.time J L n+LightSourceFlagArray.time n J L U+200
def word (J L p U V cap : ℕ) : ℕ :=
  LightBlockSourceHashes.word J L p U+LightSourceMaskFlags.word J L p U V cap
def space (work J L U : ℕ) : ℕ :=
  max (LightBlockSourceHashes.space work J L) (LightSourceMaskFlags.space work J L U)
structure Procs (P : Program) (pMain : ℕ) where
  pHashes : ℕ
  pFlags : ℕ
  hashes : LightBlockSourceHashes.Procs P pHashes
  flags : LightSourceFlagArray.Procs P pFlags
  main : P[pMain]? = some (body pHashes pFlags)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 7,LightBlockSourceHashes.body 2 5,LightBlockCoefficients.body 3 4,
    powTableBody,LightScaleArray.body,LightMaskHashes.body 3 6,LightOneHot.body 6,
    LightSourceFlagArray.body 8,LightSourceMaskFlags.body 9 12,
    LightMaskBits.body 10 11,powTableBody,LightMaskErase.body 11,
    LightSourceTrim.body 13,LightSourceRowFlag.body 14 15 16,LightSourceRowScan.body,
    emodBody,LightSourceFlagTest.body]
def programProcs : Procs program 0 :=
  ⟨1,7,⟨2,3,4,5,6,rfl,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨8,⟨9,10,11,12,rfl,rfl,rfl,⟨13,14,15,16,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩
end ThreeSum.LightSourcePreparation


