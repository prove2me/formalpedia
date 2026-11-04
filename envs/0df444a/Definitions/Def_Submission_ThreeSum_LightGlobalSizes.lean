-- Prove2me | Definitions.Def_Submission_ThreeSum_LightGlobalSizes
-- name    : Submission_ThreeSum_LightGlobalSizes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:58:42.863173+00:00
-- url     : https://prove2.me/theorems/e7f62036-92a0-450b-943c-1aa83130b4c8
-- title:
--   Light Global Sizes
-- statement:
--   Definitions and structural lemmas for Light Global Sizes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalSizes.lean

import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_BandScales
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightGlobalSizes
set_option maxHeartbeats 1000000
open Light LocalCoverBounds
def divisor (mu : ℕ) : ℕ := 2^(mu/20)
def root (C J : ℕ) : ℕ := rootCeiling (C^J)
def numerator (C J mu : ℕ) : ℕ := root C J+divisor mu-1
def band (C J mu : ℕ) : ℕ := numerator C J mu/divisor mu
def values (C p J mu : ℕ) : List ℤ :=
  [((C^J : ℕ) : ℤ),((p^J : ℕ) : ℤ),root C J,divisor mu,band C J mu]
def body (pPower pDiv pSqrt : ℕ) : Stmt :=
  .call pPower [v 0,v 2] 5 ;;
  .call pPower [v 1,v 2] 6 ;;
  .call pDiv [v 3,k 20] 7 ;;
  .call pPower [k 2,v 7] 8 ;;
  .call pSqrt [v 5 -' k 1] 9 ;;
  .set 10 (v 9 +' k 1) ;;
  .set 11 (v 10 +' v 8 -' k 1) ;;
  .call pDiv [v 11,v 8] 12 ;;
  .store (v 4) (v 5) ;;
  .store (v 4 +' k 1) (v 6) ;;
  .store (v 4 +' k 2) (v 10) ;;
  .store (v 4 +' k 3) (v 8) ;;
  .store (v 4 +' k 4) (v 12) ;;
  .set 0 (v 6)
def time (C J mu : ℕ) : ℕ := 2*LightNatPower.time J+
  LightSmallDivide.time mu 20+LightNatPower.time (mu/20)+sqrtTime (C^J-1)+
  LightSmallDivide.time (numerator C J mu) (divisor mu)+300
def word (C p J mu : ℕ) : ℕ := 1000*(C+p+J+mu+C^J+p^J+divisor mu+1)
structure Procs (P : Program) (pMain : ℕ) where
  pPower : ℕ
  pDiv : ℕ
  pSqrt : ℕ
  power : P[pPower]? = some LightNatPower.body
  divide : P[pDiv]? = some LightSmallDivide.body
  sqrt : P[pSqrt]? = some sqrtBody
  main : P[pMain]? = some (body pPower pDiv pSqrt)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1 2 3,LightNatPower.body,LightSmallDivide.body,sqrtBody]
def procs : Procs program 0 := ⟨1,2,3,rfl,rfl,rfl,rfl⟩
def localCount (n : ℕ) : ℕ :=
  outputCount (512*Scales.microHalf (Scales.inputBits n)) (Scales.microHalf (Scales.inputBits n))
end ThreeSum.LightGlobalSizes


