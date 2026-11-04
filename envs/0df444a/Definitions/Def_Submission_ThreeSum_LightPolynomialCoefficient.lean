-- Prove2me | Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
-- name    : Submission_ThreeSum_LightPolynomialCoefficient
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:52:59.954075+00:00
-- url     : https://prove2.me/theorems/f3507fde-e085-4800-9212-18beca9368d7
-- title:
--   Light Polynomial Coefficient
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialCoefficient.lean

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
namespace ThreeSum.LightPolynomialCoefficient
open Light Finset
set_option maxHeartbeats 2000000
def term (f g : ℕ → ℕ) (m k i : ℕ) : ℕ :=
  if i≤k ∧ k-i<m then f i*g (k-i) else 0
def rawCoefficient (f g : ℕ → ℕ) (n m k : ℕ) : ℕ :=
  ∑ i ∈ range n, term f g m k i
def coefficient (p : ℕ) (f g : ℕ → ℕ) (n m k : ℕ) : ℕ :=
  rawCoefficient f g n m k % p
def loopBody : Stmt :=
  .ite (v 6 ≤' v 4)
    (.ite (v 4 -' v 6 <' v 3)
      (.set 5 (v 5 +' M (v 0 +' v 6) *' M (v 1 +' (v 4 -' v 6))))
      .skip)
    .skip
def body : Stmt := .set 5 (k 0) ;; .for 6 (v 2) loopBody ;; .set 0 (v 5)
def time (n : ℕ) : ℕ := 100*n+30
variable {lim : Limits} {P : Program} {depth : ℕ}
def reducedBody (pRaw pDigit : ℕ) : Stmt :=
  .call pRaw [v 0,v 1,v 2,v 3,v 4] 6 ;;
  .call pDigit [v 6,k 1,v 5] 0
def reducedTime (n p : ℕ) : ℕ := time n+40*(n*p^2+1)+200
end ThreeSum.LightPolynomialCoefficient


