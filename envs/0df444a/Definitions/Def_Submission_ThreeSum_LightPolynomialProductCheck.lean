-- Prove2me | Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
-- name    : Submission_ThreeSum_LightPolynomialProductCheck
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:54:25.777517+00:00
-- url     : https://prove2.me/theorems/73df46cd-71c9-4511-b0c1-1afd65b74cd0
-- title:
--   Light Polynomial Product Check
-- statement:
--   Definitions and structural lemmas for Light Polynomial Product Check, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialProductCheck.lean

import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
namespace ThreeSum.LightPolynomialProductCheck
open Light
set_option maxHeartbeats 2000000
noncomputable local instance _p2m_local_instance_3bb6a27167_6 (Q : Prop) : Decidable Q := Classical.propDecidable Q
abbrev coefficient := LightPolynomialCoefficient.coefficient
def Valid (p : ℕ) (f g expected : ℕ → ℕ) (n m len : ℕ) : Prop :=
  ∀ k<len, expected k=coefficient p f g n m k
noncomputable def flag (p : ℕ) (f g expected : ℕ → ℕ) (n m len : ℕ) : ℤ :=
  if Valid p f g expected n m len then 1 else 0
def roundBody (pCoefficient : ℕ) : Stmt :=
  .call pCoefficient [v 0,v 1,v 3,v 4,v 8,v 6] 9 ;;
  .ite (.eq (v 9) (M (v 2 +' v 8))) .skip (.set 7 (k 0))
def body (pCoefficient : ℕ) : Stmt :=
  .set 7 (k 1) ;; .for 8 (v 5) (roundBody pCoefficient) ;; .set 0 (v 7)
def time (n p len : ℕ) : ℕ := len*(LightPolynomialCoefficient.reducedTime n p+100)+30
def Inv (μ : ℕ → ℤ) (srcA srcB dst n m len p : ℕ) (f g expected : ℕ → ℕ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ r : ℤ, σ=⟨frame [srcA,srcB,dst,n,m,len,p,flag p f g expected n m i,i,r],μ⟩
variable {lim : Limits} {P : Program} {depth : ℕ}
end ThreeSum.LightPolynomialProductCheck


