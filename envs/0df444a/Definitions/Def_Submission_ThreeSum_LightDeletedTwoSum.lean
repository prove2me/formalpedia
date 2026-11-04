-- Prove2me | Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum
-- name    : Submission_ThreeSum_LightDeletedTwoSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:33:28.744553+00:00
-- url     : https://prove2.me/theorems/c60dad10-3311-4b71-9704-a7626edb9e90
-- title:
--   Light Deleted Two Sum
-- statement:
--   Definitions and structural lemmas for Light Deleted Two Sum, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDeletedTwoSum.lean

import Definitions.Def_Submission_ThreeSum_LightColoredTwoSum
import Definitions.Def_Submission_ThreeSum_LightOriginalBucketFilter
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightDeletedTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
def Hit (ids : ℕ → ℕ) (values scan target : ℕ → ℤ) (targetN scanN j : ℕ) (sign : ℤ) : Prop :=
  ∃ i<j, LightColoredTwoSum.Hit scan target targetN scanN (values (ids i)) sign
def flag (ids : ℕ → ℕ) (values scan target : ℕ → ℤ) (targetN scanN j : ℕ) (sign : ℤ) : ℕ :=
  if Hit ids values scan target targetN scanN j sign then 1 else 0
def roundBody (pTwoSum : ℕ) : Stmt :=
  .set 13 (M (v 0 +' v 12)) ;;
  .set 14 (M (v 2 +' v 13)) ;;
  .call pTwoSum [v 4,v 5,v 6,v 7,v 8,v 9,v 14,v 10] 15 ;;
  .ite (k 0 <' v 15) (.set 11 (k 1)) .skip
def body (pTwoSum : ℕ) : Stmt := .set 11 (k 0) ;; .for 12 (v 1) (roundBody pTwoSum) ;; .set 0 (v 11)
def time (badN scanN L : ℕ) : ℕ := badN*(LightColoredTwoSum.time scanN L+200)+100
def Inv (μ : ℕ → ℤ) (badBase badN valuesBase originalN scanBase scanN targetBase targetN powers L : ℕ)
    (sign : ℤ) (ids : ℕ → ℕ) (values scan target : ℕ → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ index bad result : ℤ,
    σ=⟨frame [badBase,badN,valuesBase,originalN,scanBase,scanN,targetBase,targetN,powers,L,sign,
      flag ids values scan target targetN scanN j sign,j,index,bad,result],μ⟩
variable {lim : Limits} {P : Program}
def program : Program := [body 1,LightColoredTwoSum.body 2,LightBandLookup.body 3,LightBandLookup.searchBody 3]
end ThreeSum.LightDeletedTwoSum


