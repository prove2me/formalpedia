-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalParameters
-- name    : Submission_ThreeSum_LightLocalParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:39:56.47914+00:00
-- url     : https://prove2.me/theorems/7cda2b70-8173-4734-a799-e1546695be16
-- title:
--   Light Local Parameters
-- statement:
--   Definitions and structural lemmas for Light Local Parameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalParameters.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCounts
import Definitions.Def_Submission_ThreeSum_LightSelectedPrime
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightLocalParameters
open Light LocalCoverBounds
def numerator (h : ℕ) : ℕ :=
  4*(localPrime h+vertexCount (512*h) h)+localPrime h-1
def values (h : ℕ) : List ℤ :=
  LightLocalCounts.values h ++ [(localPrime h : ℤ),localBucketCap h]
def body (pCounts pPrime pDiv : ℕ) : Stmt :=
  .call pCounts [v 0,v 1,v 2] 3 ;;
  .call pPrime [v 3,v 2] 4 ;;
  .set 5 (M (v 1 +' k 1)) ;;
  .set 6 (k 4 *' (v 4 +' v 5) +' v 4 -' k 1) ;;
  .call pDiv [v 6,v 4] 7 ;;
  .store (v 1 +' k 6) (v 4) ;;
  .store (v 1 +' k 7) (v 7) ;;
  .set 0 (v 4)
def time (h : ℕ) : ℕ := LightLocalCounts.time h+
  LightSelectedPrime.time (localThreshold h)+
  LightSmallDivide.time (numerator h) (localPrime h)+200
def space (work h : ℕ) : ℕ :=
  max (LightLocalCounts.space work h) (LightSelectedPrime.space work (localThreshold h))
def word (h : ℕ) : ℕ := LightLocalCounts.word h+
  LightSelectedPrime.word (localThreshold h)+20*(localPrime h+vertexCount (512*h) h+1)
structure Procs (P : Program) (pMain : ℕ) where
  pCounts : ℕ
  pPrime : ℕ
  pDiv : ℕ
  counts : LightLocalCounts.Procs P pCounts
  prime : LightSelectedPrime.Procs P pPrime
  divide : P[pDiv]? = some LightSmallDivide.body
  main : P[pMain]? = some (body pCounts pPrime pDiv)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 9 14,LightLocalCounts.body 2,LightSubsetSetup.body 3 7 8,
    LightPascal.buildBody 4 5,fillBody,LightPascal.rowBody 6,LightArray.linearBody,
    powTableBody,LightSubsetAddress.rankBody 8,
    LightSelectedPrime.body 10 11,sqrtBody,LightPrimePool.body 12,
    LightPrimality.body 13,emodBody,LightSmallDivide.body]
def procs : Procs program 0 :=
  ⟨1,9,14,⟨2,3,4,5,6,7,8,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,
    ⟨10,11,rfl,⟨12,⟨13,rfl,rfl⟩,rfl⟩,rfl⟩,rfl,rfl⟩
end ThreeSum.LightLocalParameters


