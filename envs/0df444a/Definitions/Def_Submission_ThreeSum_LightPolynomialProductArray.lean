-- Prove2me | Definitions.Def_Submission_ThreeSum_LightPolynomialProductArray
-- name    : Submission_ThreeSum_LightPolynomialProductArray
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:05:28.919163+00:00
-- url     : https://prove2.me/theorems/5d1ae31c-172f-4191-827b-08a061469e2a
-- title:
--   Light Polynomial Product Array
-- statement:
--   Definitions and structural lemmas for Light Polynomial Product Array, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialProductArray.lean

import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Definitions.Def_Submission_ThreeSum_LightCoefficientDecode
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightPolynomialProductArray
open Light
set_option maxHeartbeats 2000000
def body (pCoefficient : ℕ) : Stmt :=
  .for 7 (v 4) (
    .call pCoefficient [v 0,v 1,v 2,v 3,v 7,v 5] 8 ;;
    .store (v 6 +' v 7) (v 8))
def time (n p len : ℕ) : ℕ := len*(LightPolynomialCoefficient.reducedTime n p+100)+10
def Inv (μ : ℕ → ℤ) (srcA srcB n m len p dst : ℕ) (f g : ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ), σ=⟨frame [srcA,srcB,n,m,len,p,dst,i,r],ν⟩ ∧
    (∀ k < i, ν (dst+k)=(LightPolynomialCoefficient.coefficient p f g n m k : ℤ)) ∧
    SameOutside μ ν dst len
variable {lim : Limits} {P : Program} {depth : ℕ}
end ThreeSum.LightPolynomialProductArray


