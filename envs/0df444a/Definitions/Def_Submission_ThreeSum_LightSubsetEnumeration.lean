-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
-- name    : Submission_ThreeSum_LightSubsetEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:26:27.202718+00:00
-- url     : https://prove2.me/theorems/21d0e497-9919-4991-8e42-fa57c2fc21de
-- title:
--   Light Subset Enumeration
-- statement:
--   Definitions and structural lemmas for Light Subset Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetEnumeration.lean

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSubsetEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def output (L k pref : ℕ) : List ℤ :=
  (enumerateLayer L k).map (fun m => ((pref+m : ℕ) : ℤ))
def body (pSelf : ℕ) : Stmt :=
  .ite (v 1 <' k 1)
    (.store (v 3) (v 2) ;; .set 0 (k 1))
    (.ite (v 0 <' v 1)
      (.set 0 (k 0))
      (.set 5 (v 0 -' k 1) ;;
        .call pSelf [v 5,v 1,v 2,v 3,v 4] 6 ;;
        .call pSelf [v 5,v 1 -' k 1,v 2 +' M (v 4 +' v 5),v 3 +' v 6,v 4] 7 ;;
        .set 0 (v 6 +' v 7)))
def time (L k : ℕ) : ℕ := 150*enumerationWork L k
def program : Program := [body 0]
end ThreeSum.LightSubsetEnumeration


