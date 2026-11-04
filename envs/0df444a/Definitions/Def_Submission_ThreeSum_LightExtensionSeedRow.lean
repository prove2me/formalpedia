-- Prove2me | Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow
-- name    : Submission_ThreeSum_LightExtensionSeedRow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:54:24.038615+00:00
-- url     : https://prove2.me/theorems/1b077f71-cddd-4e58-9918-a72ee913d007
-- title:
--   Light Extension Seed Row
-- statement:
--   Definitions and structural lemmas for Light Extension Seed Row, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionSeedRow.lean

import Definitions.Def_Submission_ThreeSum_LightCoefficientDecode
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightExtensionSeedRow
open Light
set_option maxHeartbeats 2000000
def trajectory (mul : ℕ → ℕ → ℕ) (x y : ℕ) : ℕ → ℕ
  | 0 => y
  | i+1 => mul (trajectory mul x y i) x
def roundBody (pDigit : ℕ) : Stmt :=
  .call pDigit [v 7,k 1,v 2] 9 ;;
  .store (v 5 +' v 8) (v 9) ;;
  .set 7 (M (v 0 +' v 7 *' v 1 +' v 3))
def body (pDigit : ℕ) : Stmt :=
  .set 7 (v 4) ;; .for 8 (v 6) (roundBody pDigit) ;; .set 0 (v 7)
def time (len q : ℕ) : ℕ := len*(LightRadixDigit.time q+100)+30
def word (len q p : ℕ) : ℕ := 10*(q*q+q+p+len+10)
def Inv (μ : ℕ → ℤ) (table q p x y dst len : ℕ) (mul : ℕ → ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (old : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [table,q,p,x,y,dst,len,trajectory mul x y i,i,old],ν⟩ ∧
    (∀ j < i, ν (dst+j)=(((trajectory mul x y j)%p : ℕ) : ℤ)) ∧ SameOutside μ ν dst len
variable {lim : Limits} {P : Program} {depth : ℕ}
def program : Program := [body 1,LightRadixDigit.body 2,LightSmallDivide.body]
end ThreeSum.LightExtensionSeedRow


