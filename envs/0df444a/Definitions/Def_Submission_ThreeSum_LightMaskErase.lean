-- Prove2me | Definitions.Def_Submission_ThreeSum_LightMaskErase
-- name    : Submission_ThreeSum_LightMaskErase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:26:27.568439+00:00
-- url     : https://prove2.me/theorems/d8a738c1-a257-41f3-864f-367ab4a5a91a
-- title:
--   Light Mask Erase
-- statement:
--   Definitions and structural lemmas for Light Mask Erase, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskErase.lean

import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightMaskErase
open Light ThreeSum.MaskErase ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def body (pSelf : ℕ) : Stmt :=
  .ite (k 0 <' v 0)
    (.set 5 (v 0 -' k 1) ;;
      .ite (v 2 <' M (v 4 +' v 5))
        (.call pSelf [v 5,v 1,v 2,v 3,v 4] 0)
        (.ite (v 1 =' v 5)
          (.set 0 (v 2 -' M (v 4 +' v 5)))
          (.call pSelf [v 5,v 1,v 2 -' M (v 4 +' v 5),v 3,v 4] 0 ;;
            .set 0 (M (v 4 +' v 5) +' v 0))))
    (.set 0 (k 0))
def time (L : ℕ) : ℕ := 100*L+30
def program : Program := [body 0]
end ThreeSum.LightMaskErase


