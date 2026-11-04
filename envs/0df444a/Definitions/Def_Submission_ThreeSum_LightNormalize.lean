-- Prove2me | Definitions.Def_Submission_ThreeSum_LightNormalize
-- name    : Submission_ThreeSum_LightNormalize
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:19.709572+00:00
-- url     : https://prove2.me/theorems/f5e3c413-dddf-476b-aca8-c34b7302e93d
-- title:
--   Light Normalize
-- statement:
--   Definitions and structural lemmas for Light Normalize, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNormalize.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Mathlib.Data.List.Dedup
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightNormalize
open Light
variable {lim : Limits} {P : Program}
def emitBody (pSelf : ℕ) : Stmt :=
  .store (v 2) (M (v 0)) ;;
  .call pSelf [v 0 +' k 1,v 1 -' k 1,v 2 +' k 1] 3 ;;
  .set 0 (v 3 +' k 1)
def dedupBody (pSelf : ℕ) : Stmt :=
  .ite (k 0 <' v 1)
    (.ite (k 1 <' v 1)
      (.ite (M (v 0) =' M (v 0 +' k 1))
        (.call pSelf [v 0 +' k 1,v 1 -' k 1,v 2] 0)
        (emitBody pSelf))
      (emitBody pSelf))
    (.set 0 (k 0))
def dedupTime (n : ℕ) : ℕ := 200*n+30
def body (pSort pDedup : ℕ) : Stmt :=
  .call pSort [v 1,v 0,v 3] 4 ;;
  .call pDedup [v 0,v 1,v 2] 0
def time (n : ℕ) : ℕ := sortTime n+dedupTime n+80
def space (work n : ℕ) : ℕ := work+n
structure Procs (P : Program) (pMain : ℕ) where
  pSort : ℕ
  pHalf : ℕ
  pMerge : ℕ
  pCopy : ℕ
  pDedup : ℕ
  sort : MergeSort.Procs P pSort pHalf pMerge pCopy
  dedup : P[pDedup]? = some (dedupBody pDedup)
  main : P[pMain]? = some (body pSort pDedup)
def program : Program :=
  [body 1 5,sortBody 1 2 3 4,halfBody,mergeBody,copyBody,dedupBody 5]
def program_procs : Procs program 0 := ⟨1,2,3,4,5,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩
end ThreeSum.LightNormalize


