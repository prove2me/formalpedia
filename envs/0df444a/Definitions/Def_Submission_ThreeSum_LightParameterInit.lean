-- Prove2me | Definitions.Def_Submission_ThreeSum_LightParameterInit
-- name    : Submission_ThreeSum_LightParameterInit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:43:06.866232+00:00
-- url     : https://prove2.me/theorems/325bb8cd-9ab3-487c-9029-407ca930804d
-- title:
--   Light Parameter Init
-- statement:
--   Definitions and structural lemmas for Light Parameter Init, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightParameterInit.lean

import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_LightGlobalSizes
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightParameterInit
open Light LocalCoverBounds Scales
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
def half (n : ℕ) : ℕ := microHalf (inputBits n)
def values (n : ℕ) : List ℤ :=
  ((LightScales.values n ++ LightLocalParameters.values (half n)) ++
    LightGlobalSizes.values (LightGlobalSizes.localCount n) (localRadix n)
      (blockCount (inputBits n)) (mu n)) ++ [(primeWindow n : ℤ)]
def body (pCore pLocal pGlobal pSqrt pPower : ℕ) : Stmt :=
  .call pCore [v 0,v 1] 3 ;;
  .set 4 (M (v 1 +' k 1)) ;;
  .call pLocal [v 4,v 1 +' k 5,v 2] 5 ;;
  .set 6 (M (v 1 +' k 3)) ;;
  .set 7 (M (v 1 +' k 5)) ;;
  .call pGlobal [v 7,v 5,v 6,v 3,v 1 +' k 13] 8 ;;
  .set 9 (M (v 1)) ;;
  .call pSqrt [v 9] 10 ;;
  .set 11 (v 10 +' k 1) ;;
  .call pPower [k 2,v 11] 12 ;;
  .store (v 1 +' k 18) (v 12) ;;
  .set 0 (v 8)
def time (n : ℕ) : ℕ := LightScales.time n+LightLocalParameters.time (half n)+
  LightGlobalSizes.time (LightGlobalSizes.localCount n) (blockCount (inputBits n)) (mu n)+
  sqrtTime (inputBits n)+LightNatPower.time (windowExponent (inputBits n))+400
def space (work n : ℕ) : ℕ := LightLocalParameters.space work (half n)
def word (n : ℕ) : ℕ := 1000*(n+1)+LightLocalParameters.word (half n)+
  LightGlobalSizes.word (LightGlobalSizes.localCount n) (localRadix n)
    (blockCount (inputBits n)) (mu n)+100*(primeWindow n+inputBits n+1)
structure Procs (P : Program) (pMain : ℕ) where
  pCore : ℕ
  pLocal : ℕ
  pGlobal : ℕ
  pSqrt : ℕ
  pPower : ℕ
  core : LightScales.Procs P pCore
  localParams : LightLocalParameters.Procs P pLocal
  globalSizes : LightGlobalSizes.Procs P pGlobal
  sqrt : P[pSqrt]? = some sqrtBody
  power : P[pPower]? = some LightNatPower.body
  main : P[pMain]? = some (body pCore pLocal pGlobal pSqrt pPower)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 6 20 16 21,
    LightScales.body 2 3 4 5,log2Body,cbrtCeilBody,halfBody,LightSmallDivide.body,
    LightLocalParameters.body 7 15 5,LightLocalCounts.body 8,LightSubsetSetup.body 9 13 14,
    LightPascal.buildBody 10 11,fillBody,LightPascal.rowBody 12,LightArray.linearBody,
    powTableBody,LightSubsetAddress.rankBody 14,
    LightSelectedPrime.body 16 17,sqrtBody,LightPrimePool.body 18,LightPrimality.body 19,emodBody,
    LightGlobalSizes.body 21 5 16,LightNatPower.body]
def procs : Procs program 0 :=
  ⟨1,6,20,16,21,
    ⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨7,15,5,⟨8,9,10,11,12,13,14,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,
      ⟨16,17,rfl,⟨18,⟨19,rfl,rfl⟩,rfl⟩,rfl⟩,rfl,rfl⟩,
    ⟨21,5,16,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩
end ThreeSum.LightParameterInit


