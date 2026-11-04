-- Prove2me | Definitions.Def_Submission_ThreeSum_LightGlobalKeys
-- name    : Submission_ThreeSum_LightGlobalKeys
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:16:16.178238+00:00
-- url     : https://prove2.me/theorems/c568ebb9-0f68-4726-986d-19628d419d88
-- title:
--   Light Global Keys
-- statement:
--   Definitions and structural lemmas for Light Global Keys, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalKeys.lean

import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightGlobalKeys
open Light GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open LightSubsetAddress SubsetAddress
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
def body (pEnum pLocal pGlobal : ℕ) : Stmt :=
  .set 8 (v 2 *' v 6) ;;
  .set 9 (v 7 +' v 6) ;;
  .set 10 (v 9 +' v 8) ;;
  .call pEnum [v 0,v 1,v 7,v 10] 11 ;;
  .call pLocal [v 0,v 7,v 11,v 5,v 2,v 9,v 10] 12 ;;
  .call pGlobal [v 9,v 8,v 4,v 3,v 10] 0
def localCount (h : ℕ) : ℕ := scheduleSize h*outputCount (512*h) h
def scratch (free h : ℕ) : ℕ := free+outputCount (512*h) h+localCount h
def space (free h J : ℕ) : ℕ :=
  max (LightLocalKeyRow.space (scratch free h) (512*h) (outputCount (512*h) h))
    (LightRadixKeys.space (scratch free h) (localCount h) J)
def word (h J : ℕ) : ℕ := 2^(512*h+1)+
  LightLocalKeys.word (512*h) (localPrime h) (scheduleSize h)+
  LightRadixKeys.word (localPrime h) (512*h*localPrime h) J+J+512
def time (h J : ℕ) : ℕ := LightSubsetEnumerationSetup.time (512*h) (2*h)+
  LightLocalKeys.time (512*h) (outputCount (512*h) h) (scheduleSize h)+
  LightRadixKeys.time (localCount h) J+200
structure Procs (P : Program) (pMain : ℕ) where
  pEnum : ℕ
  pPowers : ℕ
  pLayer : ℕ
  pLocal : ℕ
  pGlobal : ℕ
  pRows : ℕ
  pAffine : ℕ
  main : P[pMain]? = some (body pEnum pLocal pGlobal)
  enum : P[pEnum]? = some (LightSubsetEnumerationSetup.body pPowers pLayer)
  powers : P[pPowers]? = some powTableBody
  layer : P[pLayer]? = some (LightSubsetEnumeration.body pLayer)
  locals : LightLocalKeys.Procs P pLocal
  globalProc : P[pGlobal]? = some (LightRadixKeys.body pGlobal pRows)
  rows : P[pRows]? = some (LightRadixRows.body pAffine)
  affine : P[pAffine]? = some LightReportingAffine.body
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1 4 11,LightSubsetEnumerationSetup.body 2 3,powTableBody,
  LightSubsetEnumeration.body 3,LightLocalKeys.body 5 10,LightLocalKeyRow.body 6 7 9,
  fillBody,LightMaskHashes.body 2 8,LightOneHot.body 8,LightArray.linearBody,copyBody,
  LightRadixKeys.body 11 12,LightRadixRows.body 13,LightReportingAffine.body]
def programProcs : Procs program 0 :=
  ⟨1,2,3,4,11,12,13,rfl,rfl,rfl,rfl,⟨5,10,rfl,⟨6,7,2,8,9,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,
    rfl,rfl,rfl⟩
end ThreeSum.LightGlobalKeys


