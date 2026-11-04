-- Prove2me | Definitions.Def_Submission_ThreeSum_LightWeightGather
-- name    : Submission_ThreeSum_LightWeightGather
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:21:51.454195+00:00
-- url     : https://prove2.me/theorems/9147b278-38a6-46db-90c4-20cf9d605131
-- title:
--   Light Weight Gather
-- statement:
--   Definitions and structural lemmas for Light Weight Gather, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightGather.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightWeightGather
open Light
set_option maxHeartbeats 1000000
def body (pCopy : ℕ) : Stmt :=
  .for 5 (v 3) (
    .set 6 (M (v 0 +' v 5)) ;;
    .call pCopy [v 1 +' v 6 *' v 4,v 2 +' v 5 *' v 4,v 4] 7)
def time (rows width : ℕ) : ℕ := rows*(copyTime width+100)+6
def word (N rows width : ℕ) : ℕ := N+rows+width+1
def Inv (μ : ℕ → ℤ) (indices src dst rows width : ℕ) (select : ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (x r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [indices,src,dst,rows,width,i,x,r],μ'⟩ ∧
    (∀ j < i, ∀ a < width, μ' (dst+j*width+a) = μ (src+select j*width+a)) ∧
    SameOutside μ μ' dst (rows*width)
structure Procs (P : Program) (pMain : ℕ) where
  pCopy : ℕ
  copy : P[pCopy]? = some copyBody
  main : P[pMain]? = some (body pCopy)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1,copyBody]
def programProcs : Procs program 0 := ⟨1,rfl,rfl⟩
end ThreeSum.LightWeightGather


