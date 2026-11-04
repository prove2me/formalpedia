-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
-- name    : Submission_ThreeSum_LightTernaryQueryLookup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:33:31.189296+00:00
-- url     : https://prove2.me/theorems/3ab77dc2-f451-476a-bd39-4933ecfb0395
-- title:
--   Light Ternary Query Lookup
-- statement:
--   Definitions and structural lemmas for Light Ternary Query Lookup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryQueryLookup.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryQueryLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def body (pSearch : ℕ) : Stmt :=
  .call pSearch [v 0,v 1,v 2,v 4,v 5,k 0] 7 ;;
  .set 0 (M (v 3 +' v 6 *' v 1 +' v 7 -' k 1))
def time (L : ℕ) : ℕ := LightBandLookup.searchTime L + 100
def program : Program := [body 1,LightBandLookup.searchBody 1]
end ThreeSum.LightTernaryQueryLookup


