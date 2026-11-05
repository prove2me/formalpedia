-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightEnumeration
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:06:47.564688+00:00
-- url     : https://prove2.me/theorems/26415c97-eed5-4faa-9da2-216a194eb0b5
-- title:
--   LightEnumeration
-- statement:
--   Definitions and structural lemmas for LightEnumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightEnumeration.lean

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
      .ite (v 1 <' k 1369)
        (.set 0 (v 6))
        (.call pSelf [v 5,v 1 -' k 1369,
          v 2 +' M (v 4 +' k 2 *' v 5),v 3 +' v 6,v 4] 7 ;;
          .ite (v 1 <' k 2740)
            (.set 0 (v 6 +' v 7))
            (.call pSelf [v 5,v 1 -' k 2740,
              v 2 +' k 3 *' M (v 4 +' k 2 *' v 5),v 3 +' v 6 +' v 7,v 4] 8 ;;
              .set 0 (v 6 +' v 7 +' v 8))))
def time (N T : ℕ) : ℕ := 300*visits N T
def program : Program := [body 0]
end ThreeSum.LightCacheEnumeration
end WeightedCache3SUMRefinement_e1ae71d


