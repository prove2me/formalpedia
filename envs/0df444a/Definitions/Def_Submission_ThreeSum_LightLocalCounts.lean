-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCounts
-- name    : Submission_ThreeSum_LightLocalCounts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:30:58.602202+00:00
-- url     : https://prove2.me/theorems/be46c0db-dded-4e41-b3c6-168bd5c84b4f
-- title:
--   Light Local Counts
-- statement:
--   Definitions and structural lemmas for Light Local Counts, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCounts.lean

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightLocalCounts
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open Light LocalCoverBounds LightPascal LightSubsetAddress
def values (h : ℕ) : List ℤ :=
  [outputCount (512*h) h,vertexCount (512*h) h,degree (512*h) h,
    groupSize h,2^(2*h),localThreshold h]
def body (pSetup : ℕ) : Stmt :=
  .set 3 (k 512 *' v 0) ;;
  .set 4 (k 2 *' v 0) ;;
  .call pSetup [v 3,k 0,k 0,v 2] 5 ;;
  .set 6 (M (v 2 +' v 3 *' (v 3 +' k 1) +' v 4)) ;;
  .set 7 (M (v 2 +' v 3 *' (v 3 +' k 1) +' v 0)) ;;
  .set 8 (M (v 2 +' (v 3 -' v 0) *' (v 3 +' k 1) +' v 0)) ;;
  .set 9 (M (v 2 +' v 4 *' (v 3 +' k 1) +' v 0)) ;;
  .set 10 (M (v 2 +' (v 3 +' k 1) *' (v 3 +' k 1) +' v 4)) ;;
  .set 11 (v 6 *' v 10) ;;
  .store (v 1) (v 6) ;;
  .store (v 1 +' k 1) (v 7) ;;
  .store (v 1 +' k 2) (v 8) ;;
  .store (v 1 +' k 3) (v 9) ;;
  .store (v 1 +' k 4) (v 10) ;;
  .store (v 1 +' k 5) (v 11) ;;
  .set 0 (v 11)
def time (h : ℕ) : ℕ := LightSubsetSetup.time (512*h)+500
def space (work h : ℕ) : ℕ := work+tableSize (512*h)+(512*h+1)
def word (h : ℕ) : ℕ := 1024+4*(2^(512*h+1))^2
structure Procs (P : Program) (pMain : ℕ) where
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pPowers : ℕ
  pRank : ℕ
  setup : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  main : P[pMain]? = some (body pSetup)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1,LightSubsetSetup.body 2 6 7,buildBody 3 4,fillBody,rowBody 5,
    LightArray.linearBody,powTableBody,rankBody 7]
def procs : Procs program 0 := ⟨1,2,3,4,5,6,7,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
end ThreeSum.LightLocalCounts


