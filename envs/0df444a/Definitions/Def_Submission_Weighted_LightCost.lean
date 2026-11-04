-- Prove2me | Definitions.Def_Submission_Weighted_LightCost
-- name    : Submission_Weighted_LightCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:39:25.677794+00:00
-- url     : https://prove2.me/theorems/f82979f4-b622-4041-a3e2-239084e93e6e
-- title:
--   Light Cost
-- statement:
--   Definitions and structural lemmas for Light Cost, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightCost.lean

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightWeightedCost
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
open ThreeSum.WeightedEnumeration
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress
def digitAt (N m i : ℕ) : ℕ := LightTernaryCodes.digit (2*N)
  (2*(N-1-i)) (2*(N-1-i)+1) m
def partialCost (N m j : ℕ) : ℕ := ∑ i ∈ range j, digitCost (digitAt N m i)
def roundBody (pDigit : ℕ) : Stmt :=
  .set 5 (k 2 *' (v 0 -' k 1 -' v 4)) ;;
  .call pDigit [k 2 *' v 0,v 5,v 5 +' k 1,v 1,v 2] 6 ;;
  .ite (v 6 =' k 2) (.set 3 (v 3 +' k 1025)) (.set 3 (v 3 +' k 512 *' v 6))
def body (pDigit : ℕ) : Stmt :=
  .set 3 (k 0) ;; .for 4 (v 0) (roundBody pDigit) ;; .set 0 (v 3)
def time (N : ℕ) : ℕ := N*(LightTernaryCodes.digitTime (2*N)+200)+100
def Inv (N m powers : ℕ) (μ : ℕ → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ lo res : ℤ, σ=⟨frame [N,m,powers,partialCost N m j,j,lo,res],μ⟩
variable {lim : Limits} {P : Program}
def program : Program :=
  [body 1,LightTernaryCodes.digitBody 2,LightMaskErase.body 2]
end ThreeSum.LightWeightedCost


