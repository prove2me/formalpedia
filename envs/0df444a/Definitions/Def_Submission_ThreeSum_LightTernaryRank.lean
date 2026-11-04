-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryRank
-- name    : Submission_ThreeSum_LightTernaryRank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:39:00.898184+00:00
-- url     : https://prove2.me/theorems/7b3fd623-2895-4e5e-9a25-b7ef9f5f8f02
-- title:
--   Light Ternary Rank
-- statement:
--   Definitions and structural lemmas for Light Ternary Rank, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRank.lean

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryRank
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress
def digitAt (N m i : ℕ) : ℕ := LightTernaryCodes.digit (2*N)
  (2*(N-1-i)) (2*(N-1-i)+1) m
def partialRank (N m j : ℕ) : ℕ := ∑ i ∈ range j, digitAt N m i
def roundBody (pDigit : ℕ) : Stmt :=
  .set 5 (k 2 *' (v 0 -' k 1 -' v 4)) ;;
  .call pDigit [k 2 *' v 0,v 5,v 5 +' k 1,v 1,v 2] 6 ;;
  .set 3 (v 3 +' v 6)
def body (pDigit : ℕ) : Stmt :=
  .set 3 (k 0) ;; .for 4 (v 0) (roundBody pDigit) ;; .set 0 (v 3)
def time (N : ℕ) : ℕ := N*(LightTernaryCodes.digitTime (2*N)+150)+100
def Inv (N m powers : ℕ) (μ : ℕ → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ lo res : ℤ, σ=⟨frame [N,m,powers,partialRank N m j,j,lo,res],μ⟩
variable {lim : Limits} {P : Program}
def program : Program :=
  [body 1,LightTernaryCodes.digitBody 2,LightMaskErase.body 2]
end ThreeSum.LightTernaryRank


