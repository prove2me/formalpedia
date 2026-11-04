-- Prove2me | Definitions.Def_Submission_ThreeSum_LightQueryBox
-- name    : Submission_ThreeSum_LightQueryBox
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:44:37.761399+00:00
-- url     : https://prove2.me/theorems/f923d096-a97a-4647-88d2-3ca9a8362442
-- title:
--   Light Query Box
-- statement:
--   Definitions and structural lemmas for Light Query Box, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryBox.lean

import Definitions.Def_Submission_ThreeSum_LightStageLookup
import Definitions.Def_Submission_ThreeSum_LightMaskMinimum
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightQueryBox
open Light ThreeSum.SubsetAddress ThreeSum.MaskDifference
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def body (pMinimum pLookup : ℕ) : Stmt :=
  .set 8 (v 2 -' v 4) ;;
  .set 9 (v 3 -' v 5) ;;
  .ite (v 5 =' k 0) (.set 10 (v 0))
    (.call pMinimum [v 0,v 5,v 7] 10) ;;
  .call pLookup [v 0,v 1,v 8,v 9,v 10,v 6,v 7] 0
def time (L : ℕ) : ℕ := LightMaskMinimum.time L+LightStageLookup.time L+120
def program : Program :=
  [body 1 2,LightMaskMinimum.body 8 11,LightStageLookup.body 3 4,
    LightDownsetSize.body 5 10,LightDownsetAddress.body 5 10,
    LightSubsetSetup.body 6 8 9,buildBody 7 12,fillBody,powTableBody,
    rankBody 9,LightSubsetOffset.body,LightMaskErase.body 11,rowBody 13,LightArray.linearBody]
end ThreeSum.LightQueryBox


