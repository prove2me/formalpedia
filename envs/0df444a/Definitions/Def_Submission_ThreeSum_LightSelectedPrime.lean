-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSelectedPrime
-- name    : Submission_ThreeSum_LightSelectedPrime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:37:20.865105+00:00
-- url     : https://prove2.me/theorems/05c3ce0c-634f-4e36-acb0-173007eca935
-- title:
--   Light Selected Prime
-- statement:
--   Definitions and structural lemmas for Light Selected Prime, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSelectedPrime.lean

import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSelectedPrime
open Light LocalCoverBounds LightResidues
set_option maxHeartbeats 1000000
def body (pSqrt pPool : ℕ) : Stmt :=
  .call pSqrt [v 0 -' k 1] 2 ;;
  .set 3 (v 2 +' k 1) ;;
  .call pPool [v 3,v 1] 4 ;;
  .set 0 (M (v 1))
def time (N : ℕ) : ℕ := sqrtTime (N-1)+LightPrimePool.time (rootCeiling N)+100
def space (free N : ℕ) : ℕ := LightPrimePool.space free (rootCeiling N)
def word (N : ℕ) : ℕ := 100*(N+1)
structure Procs (P : Program) (pMain : ℕ) where
  pSqrt : ℕ
  pPool : ℕ
  sqrt : P[pSqrt]? = some sqrtBody
  pool : LightPrimePool.Procs P pPool
  main : P[pMain]? = some (body pSqrt pPool)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1 2,sqrtBody,LightPrimePool.body 3,
    LightPrimality.body 4,emodBody]
def procs : Procs program 0 :=
  ⟨1,2,rfl,⟨3,⟨4,rfl,rfl⟩,rfl⟩,rfl⟩
end ThreeSum.LightSelectedPrime


