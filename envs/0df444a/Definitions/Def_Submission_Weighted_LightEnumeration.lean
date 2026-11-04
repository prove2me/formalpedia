-- Prove2me | Definitions.Def_Submission_Weighted_LightEnumeration
-- name    : Submission_Weighted_LightEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:29:47.395501+00:00
-- url     : https://prove2.me/theorems/03b88f25-a511-4be7-b7da-23a50713b9ce
-- title:
--   Light Enumeration
-- statement:
--   Definitions and structural lemmas for Light Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightEnumeration.lean

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_Weighted_Addresses
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightCacheEnumeration
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Light ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def output (N T pref : ℕ) : List ℤ :=
  (codes N T).map (fun a => ((pref+a : ℕ) : ℤ))
def body (pSelf : ℕ) : Stmt :=
  .ite (v 0 <' k 1)
    (.store (v 3) (v 2) ;; .set 0 (k 1))
    (.set 5 (v 0 -' k 1) ;;
      .call pSelf [v 5,v 1,v 2,v 3,v 4] 6 ;;
      .ite (v 1 <' k 512)
        (.set 0 (v 6))
        (.call pSelf [v 5,v 1 -' k 512,
          v 2 +' M (v 4 +' k 2 *' v 5),v 3 +' v 6,v 4] 7 ;;
          .ite (v 1 <' k 1025)
            (.set 0 (v 6 +' v 7))
            (.call pSelf [v 5,v 1 -' k 1025,
              v 2 +' k 3 *' M (v 4 +' k 2 *' v 5),v 3 +' v 6 +' v 7,v 4] 8 ;;
              .set 0 (v 6 +' v 7 +' v 8))))
def time (N T : ℕ) : ℕ := 300*visits N T
def program : Program := [body 0]
end ThreeSum.LightCacheEnumeration


