-- Prove2me | Definitions.Def_Submission_ThreeSum_LightPrimeAddArray
-- name    : Submission_ThreeSum_LightPrimeAddArray
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:05:34.559932+00:00
-- url     : https://prove2.me/theorems/08616c7d-00f1-46b0-a52b-cc414fa1afc0
-- title:
--   Light Prime Add Array
-- statement:
--   Definitions and structural lemmas for Light Prime Add Array, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeAddArray.lean

import Definitions.Def_Submission_ThreeSum_LightPrimeCoefficient
import Definitions.Def_Submission_ThreeSum_LightCoefficientDecode
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightPrimeAddArray
open Light
set_option maxHeartbeats 2000000
def body (pMulAdd : ℕ) : Stmt :=
  .for 5 (v 3) (
    .call pMulAdd [M (v 0 +' v 5),k 1,M (v 1 +' v 5),v 4] 6 ;;
    .store (v 2 +' v 5) (v 6))
def time (n p : ℕ) : ℕ := n*(LightPrimeCoefficient.mulAddTime p+60)+10
def Inv (μ : ℕ → ℤ) (srcA srcB dst n p : ℕ) (f g : ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ), σ=⟨frame [srcA,srcB,dst,n,p,i,r],ν⟩ ∧
    (∀ j < i, ν (dst+j)=(((f j+g j)%p : ℕ) : ℤ)) ∧ SameOutside μ ν dst n
variable {lim : Limits} {P : Program} {depth : ℕ}
end ThreeSum.LightPrimeAddArray


