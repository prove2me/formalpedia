-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryNearDigits
-- name    : Submission_ThreeSum_LightTernaryNearDigits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:42:14.417941+00:00
-- url     : https://prove2.me/theorems/9164d773-b7c4-4cc1-8342-e7fc2369b6c0
-- title:
--   Light Ternary Near Digits
-- statement:
--   Definitions and structural lemmas for Light Ternary Near Digits, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearDigits.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightTernaryNearDigits
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
def roundBody (pDigit : ℕ) : Stmt :=
  .set 6 (k 2 *' (v 0 -' k 1 -' v 5)) ;;
  .set 7 (v 6 +' k 1) ;;
  .call pDigit [k 2 *' v 0,v 6,v 7,v 1,v 2] 8 ;;
  .store (v 3 +' v 5) (v 8) ;;
  .store (v 4 +' v 5) (k 1)
def body (pDigit : ℕ) : Stmt := .for 5 (v 0) (roundBody pDigit)
def time (N : ℕ) : ℕ := N*(LightTernaryCodes.digitTime (2*N)+200)+20
def Inv (μ : ℕ → ℤ) (N m powers caps active j : ℕ) (σ : State) : Prop :=
  ∃ lo hi dig : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [N,m,powers,caps,active,j,lo,hi,dig],ν⟩ ∧
    SameOutside μ ν caps (active+N-caps) ∧
    (∀ i<j, ν (caps+i)=(LightTernaryRank.digitAt N m i : ℤ)) ∧
    (∀ i<j, ν (active+i)=1)
variable {lim : Limits} {P : Program}
end ThreeSum.LightTernaryNearDigits


