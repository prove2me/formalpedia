-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
-- name    : Submission_ThreeSum_LightTernaryEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:29:53.513197+00:00
-- url     : https://prove2.me/theorems/084f6e6d-a158-4061-9d4d-145729268518
-- title:
--   Light Ternary Enumeration
-- statement:
--   Definitions and structural lemmas for Light Ternary Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightTernaryEnumeration
open Light ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def output (N T pref : ℕ) : List ℤ :=
  (codes N T).map (fun a => ((pref+a : ℕ) : ℤ))
def body (pSelf : ℕ) : Stmt :=
  .ite (v 0 <' k 1)
    (.store (v 3) (v 2) ;; .set 0 (k 1))
    (.set 5 (v 0 -' k 1) ;;
      .call pSelf [v 5,v 1,v 2,v 3,v 4] 6 ;;
      .ite (v 1 <' k 1)
        (.set 0 (v 6))
        (.call pSelf [v 5,v 1 -' k 1,
          v 2 +' M (v 4 +' k 2 *' v 5),v 3 +' v 6,v 4] 7 ;;
          .ite (v 1 <' k 2)
            (.set 0 (v 6 +' v 7))
            (.call pSelf [v 5,v 1 -' k 2,
              v 2 +' k 3 *' M (v 4 +' k 2 *' v 5),v 3 +' v 6 +' v 7,v 4] 8 ;;
              .set 0 (v 6 +' v 7 +' v 8))))
def time (N T : ℕ) : ℕ := 300*visits N T
def program : Program := [body 0]
end ThreeSum.LightTernaryEnumeration


