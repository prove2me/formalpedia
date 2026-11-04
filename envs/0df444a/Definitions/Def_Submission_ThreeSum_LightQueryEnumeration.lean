-- Prove2me | Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
-- name    : Submission_ThreeSum_LightQueryEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:50:53.693202+00:00
-- url     : https://prove2.me/theorems/cf9f140a-ad84-42ec-a048-896e061402a1
-- title:
--   Light Query Enumeration
-- statement:
--   Definitions and structural lemmas for Light Query Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryEnumeration.lean

import Definitions.Def_Submission_ThreeSum_LightQueryWeights
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightQueryEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress QueryCoordinates
variable {lim : Limits} {P : Program}
def body (pWeights pEnum : ℕ) : Stmt :=
  .set 5 (v 4 +' v 0 +' k 1) ;;
  .call pWeights [v 0,v 1,v 4,v 5] 6 ;;
  .call pEnum [v 6,v 2,k 0,v 3,v 4] 0
def time (W c t : ℕ) : ℕ :=
  LightQueryWeights.time W+LightSubsetEnumeration.time c t+60
def program : Program :=
  [body 1 4,LightQueryWeights.body 2 3,powTableBody,
    LightMaskErase.body 3,LightSubsetEnumeration.body 4]
end ThreeSum.LightQueryEnumeration


