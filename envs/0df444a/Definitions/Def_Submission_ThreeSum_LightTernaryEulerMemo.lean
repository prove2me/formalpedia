-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
-- name    : Submission_ThreeSum_LightTernaryEulerMemo
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:36:46.960177+00:00
-- url     : https://prove2.me/theorems/a38bbc15-bdce-49e5-8469-110152eee498
-- title:
--   Light Ternary Euler Memo
-- statement:
--   Definitions and structural lemmas for Light Ternary Euler Memo, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMemo.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerScan
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryEulerMemo
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
def Ready (μ ν : ℕ → ℤ) (f : ℕ → ℤ) (rank : ℕ → ℕ)
    (vals rows T stage : ℕ) : Prop :=
  Kept μ ν vals ∧ ∀ j < rows, rank j ≤ T+stage → ν (vals+j)=f j
def loopBody (pScan : ℕ) : Stmt :=
  .call pScan [v 0,v 1,v 2,v 3,v 4,v 5,v 6 +' v 11 +' k 1,v 7,v 9,v 10] 12
def body (pScan : ℕ) : Stmt :=
  .for 11 (v 8 -' v 6) (loopBody pScan) ;;
  .set 0 (k 0)
def time (N rows stages V : ℕ) : ℕ :=
  stages*(LightTernaryEulerScan.time N rows V+150)+100
def Inv (μ : ℕ → ℤ) (f : ℕ → ℤ) (rank : ℕ → ℕ)
    (N rows ws ks ranks vals T h maxRank pcount fr stage : ℕ) (σ : State) : Prop :=
  ∃ (rval : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [N,rows,ws,ks,ranks,vals,T,h,maxRank,pcount,fr,stage,rval],ν⟩ ∧
      Ready μ ν f rank vals rows T stage
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1,LightTernaryEulerScan.body 2,
  LightTernaryEulerRow.fillBody 3,LightTernaryEulerRow.body 4 5,
  LightTernaryWeightedSum.body,LightTernaryDivide.body 6,LightOutputDecodeDivide.body]
end ThreeSum.LightTernaryEulerMemo


