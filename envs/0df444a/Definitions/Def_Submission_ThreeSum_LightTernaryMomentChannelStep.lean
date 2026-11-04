-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
-- name    : Submission_ThreeSum_LightTernaryMomentChannelStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:46:52.79379+00:00
-- url     : https://prove2.me/theorems/f4458ad1-2565-460b-b26a-a3965959c690
-- title:
--   Light Ternary Moment Channel Step
-- statement:
--   Definitions and structural lemmas for Light Ternary Moment Channel Step, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannelStep.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannels
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryMomentChannelStep
open Light TernaryWeightChannels
set_option maxHeartbeats 1500000
def callArgs (positions : List ℕ) : List Expr := positions.map v
def values (positions : List ℕ) (vals : List ℤ) : List ℤ := positions.map (frame vals)
def args (originalB nB originalC nC leftWeight rightWeight matrix count out : ℕ)
    (backend : List ℤ) : List ℤ :=
  [(originalB : ℤ),nB,originalC,nC,leftWeight,rightWeight,matrix,count,out]++backend
def body (k j pLeft pRight pHost pAdd : ℕ) (positions : List ℕ) (arity : ℕ) : Stmt :=
  .call pLeft [v 0,v 1,v 4] 0 ;;
  .call pRight [v 2,v 3,v 5] 0 ;;
  .call pHost (callArgs positions) 0 ;;
  .call pAdd [v 6 +' Light.k k *' v 7,v 8,v 7] 0 ;;
  .set 0 (Light.k 0)
def time (k j nB nC count hostTime hostArity : ℕ) : ℕ :=
  LightTernaryScalarChannel.time (leftMoment k j) nB+
  LightTernaryScalarChannel.time (rightMoment k j) nC+
  hostTime+LightTernaryMomentAccumulate.time count+hostArity+300
structure Procs (k j : ℕ) (positions : List ℕ) (arity : ℕ) (P : Program) (pMain : ℕ) where
  pLeft : ℕ
  pRight : ℕ
  pHost : ℕ
  pAdd : ℕ
  left : P[pLeft]?=some (LightTernaryScalarChannel.body (leftMoment k j))
  right : P[pRight]?=some (LightTernaryScalarChannel.body (rightMoment k j))
  add : P[pAdd]?=some LightTernaryMomentAccumulate.body
  main : P[pMain]?=some (body k j pLeft pRight pHost pAdd positions arity)
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightTernaryMomentChannelStep


