-- Prove2me | Definitions.Def_Submission_ThreeSum_LightDownsetAddress
-- name    : Submission_ThreeSum_LightDownsetAddress
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:30:47.825569+00:00
-- url     : https://prove2.me/theorems/0d064c62-5adb-4adb-81e8-f6c002e4f2df
-- title:
--   Light Downset Address
-- statement:
--   Definitions and structural lemmas for Light Downset Address, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetAddress.lean

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightDownsetAddress
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def body (pFresh pOffset : ℕ) : Stmt :=
  .call pFresh [v 0,v 1,v 2,v 3] 4 ;;
  .call pOffset [v 3,v 0,v 1,v 0] 5 ;;
  .set 0 (v 4 +' v 5)
def time (L : ℕ) : ℕ := LightSubsetSetup.time L + LightSubsetOffset.time L + 30
def program : Program :=
  [body 1 8, LightSubsetSetup.body 2 6 7, buildBody 3 4, fillBody, rowBody 5,
    LightArray.linearBody, powTableBody, rankBody 7, LightSubsetOffset.body]
end ThreeSum.LightDownsetAddress


