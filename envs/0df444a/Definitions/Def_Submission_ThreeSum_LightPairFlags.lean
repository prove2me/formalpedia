-- Prove2me | Definitions.Def_Submission_ThreeSum_LightPairFlags
-- name    : Submission_ThreeSum_LightPairFlags
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:29:08.279806+00:00
-- url     : https://prove2.me/theorems/83e39869-eb02-4ee8-9ffc-98d636d23fe2
-- title:
--   Light Pair Flags
-- statement:
--   Definitions and structural lemmas for Light Pair Flags, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairFlags.lean

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightTrimTest
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightPairFlags
open Light
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
def pairKey (n p : ℕ) (left right : ℕ → ℕ) (i : ℕ) : ℕ :=
  left (i/n)*p+right (i%n)
def pairFlag (L n cap : ℕ) (bits : ℕ → ℕ → ℕ)
    (left right leftCount rightCount : ℕ → ℕ) (i : ℕ) : ℕ :=
  LightTrimTest.flag (LightBooleanDot.dot (bits (i/n)) (bits (i%n)) L)
    (leftCount (left (i/n))) (rightCount (right (i%n))) cap
def roundBody (pDivide pDot pTrim : ℕ) : Stmt :=
  .call pDivide [v 11,v 6] 12 ;;
  .set 13 (v 11 -' v 12 *' v 6) ;;
  .call pDot [v 0 +' v 12 *' v 7,v 0 +' v 13 *' v 7,v 7] 14 ;;
  .set 15 (M (v 1 +' v 12)) ;;
  .set 16 (M (v 2 +' v 13)) ;;
  .call pTrim [v 14,M (v 3 +' v 15),M (v 4 +' v 16),v 9] 17 ;;
  .store (v 5 +' v 11) (v 15 *' v 8 +' v 16) ;;
  .store (v 10 +' v 11) (v 17)
def body (pDivide pDot pTrim : ℕ) : Stmt :=
  .set 10 (v 5 +' v 6 *' v 6) ;;
  .for 11 (v 6 *' v 6) (roundBody pDivide pDot pTrim)
def roundTime (L n : ℕ) : ℕ := 20*n+LightBooleanDot.time L+LightTrimTest.time+350
def time (L n : ℕ) : ℕ := n*n*(roundTime L n+12)+30
def word (L n p cap : ℕ) : ℕ := 100*(n*n+p*p+cap+L+n+p+1)
def Inv (μ : ℕ → ℤ) (bits : ℕ → ℕ → ℕ) (left right leftCount rightCount : ℕ → ℕ)
    (bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap i : ℕ) (σ : State) : Prop :=
  ∃ (a b c e f g : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [bitPtr,leftPtr,rightPtr,leftHist,rightHist,dst,n,L,p,cap,dst+n*n,i,a,b,c,e,f,g],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = (pairKey n p left right j : ℤ)) ∧
    (∀ j < i, μ' (dst+n*n+j) = (pairFlag L n cap bits left right leftCount rightCount j : ℤ)) ∧
    SameOutside μ μ' dst (2*(n*n))
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1 2 3,LightSmallDivide.body,LightBooleanDot.body,LightTrimTest.body]
end ThreeSum.LightPairFlags


