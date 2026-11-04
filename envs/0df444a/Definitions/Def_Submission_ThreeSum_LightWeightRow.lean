-- Prove2me | Definitions.Def_Submission_ThreeSum_LightWeightRow
-- name    : Submission_ThreeSum_LightWeightRow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:47:43.569595+00:00
-- url     : https://prove2.me/theorems/f2285a97-9c86-445c-a23d-a05d5664d51b
-- title:
--   Light Weight Row
-- statement:
--   Definitions and structural lemmas for Light Weight Row, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightRow.lean

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightWeightRow
open Light
set_option maxHeartbeats 1200000
def body (pDigit : ℕ) : Stmt :=
  .for 8 (v 7) (
    .call pDigit [v 2,M (v 3 +' (v 0 -' k 1 -' (v 4 +' v 5 *' v 8))),v 1] 9 ;;
    .store (v 6 +' v 8) (v 9))
def time (n k : ℕ) : ℕ := n*(LightRadixDigit.time k+100)+6
def word (W p k start stride : ℕ) : ℕ :=
  4*(k+p^(W+1)+p+W+start+stride+2)
def Inv (μ : ℕ → ℤ) (W p k powers start stride dst n i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,p,k,powers,start,stride,dst,n,i,r],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = (WeightEnumeration.digit p W k (start+stride*j) : ℤ)) ∧
    SameOutside μ μ' dst n
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1,LightRadixDigit.body 2,LightSmallDivide.body]
end ThreeSum.LightWeightRow


