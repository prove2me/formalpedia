-- Prove2me | Definitions.Def_Submission_ThreeSum_LightExtensionSeedMatrix
-- name    : Submission_ThreeSum_LightExtensionSeedMatrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:58:32.10609+00:00
-- url     : https://prove2.me/theorems/9c2c4928-39ce-40e4-ad55-e336933a456a
-- title:
--   Light Extension Seed Matrix
-- statement:
--   Definitions and structural lemmas for Light Extension Seed Matrix, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionSeedMatrix.lean

import Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightExtensionSeedMatrix
open Light
set_option maxHeartbeats 3000000
def body (pRow pDigit pDivide : ℕ) : Stmt :=
  .set 5 (v 1 *' v 1) ;;
  .for 6 (v 5) (
    .call pDivide [v 6,v 1] 7 ;;
    .call pDigit [v 6,k 1,v 1] 8 ;;
    .call pRow [v 0,v 1,v 2,v 7,v 8,v 3 +' v 6 *' v 4,v 4] 9)
def value (mul : ℕ → ℕ → ℕ) (q p row col : ℕ) : ℕ :=
  LightExtensionSeedRow.trajectory mul (row/q) (row%q) col % p
def time (len q : ℕ) : ℕ := q*q*(LightExtensionSeedRow.time len q+60*(q*q)+400)+30
def word (len q p : ℕ) : ℕ := 30*(q*q+q+p+q*q*len+len+10)
def Inv (μ : ℕ → ℤ) (table q p dst len : ℕ) (mul : ℕ → ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (x y z : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [table,q,p,dst,len,q*q,i,x,y,z],ν⟩ ∧
    (∀ r  <  i, ∀ j < len, ν (dst+r*len+j)=(value mul q p r j : ℤ)) ∧
    SameOutside μ ν dst (q*q*len)
variable {lim : Limits} {P : Program} {depth : ℕ}
def program : Program := [body 1 2 3,LightExtensionSeedRow.body 2,LightRadixDigit.body 3,LightSmallDivide.body]
end ThreeSum.LightExtensionSeedMatrix


