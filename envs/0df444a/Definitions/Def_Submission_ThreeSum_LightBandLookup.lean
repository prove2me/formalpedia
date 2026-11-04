-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandLookup
-- name    : Submission_ThreeSum_LightBandLookup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:26:29.765117+00:00
-- url     : https://prove2.me/theorems/13494294-98f4-479f-b9f5-ead0570d8fc2
-- title:
--   Light Band Lookup
-- statement:
--   Definitions and structural lemmas for Light Band Lookup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandLookup.lean

import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightBandLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def searchBody (pSelf : ℕ) : Stmt :=
  .ite (k 0 <' v 4)
    (.set 6 (v 4 -' k 1) ;;
      .set 7 (v 5 +' M (v 3 +' v 6)) ;;
      .ite (v 7 ≤' v 1)
        (.ite (v 2 <' M (v 0 +' v 7 -' k 1))
          (.call pSelf [v 0,v 1,v 2,v 3,v 6,v 5] 0)
          (.call pSelf [v 0,v 1,v 2,v 3,v 6,v 7] 0))
        (.call pSelf [v 0,v 1,v 2,v 3,v 6,v 5] 0))
    (.set 0 (v 5))
def searchTime (L : ℕ) : ℕ := 120*L+30
def result (lo hi : ℕ → ℤ) (n : ℕ) (x : ℤ) : ℕ :=
  ((BinarySearch.locate lo hi n x).map Nat.succ).getD 0
def body (pSearch : ℕ) : Stmt :=
  .call pSearch [v 0,v 2,v 3,v 4,v 5,k 0] 6 ;;
  .ite (k 0 <' v 6)
    (.ite (M (v 1 +' v 6 -' k 1) <' v 3)
      (.set 0 (k 0)) (.set 0 (v 6)))
    (.set 0 (k 0))
def time (L : ℕ) : ℕ := searchTime L+100
def program : Program := [body 1,searchBody 1]
end ThreeSum.LightBandLookup


