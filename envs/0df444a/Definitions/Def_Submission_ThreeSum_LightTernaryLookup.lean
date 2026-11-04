-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryLookup
-- name    : Submission_ThreeSum_LightTernaryLookup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:30:33.553815+00:00
-- url     : https://prove2.me/theorems/dcdbcef2-c03f-49f7-af28-b2047178ab76
-- title:
--   Light Ternary Lookup
-- statement:
--   Definitions and structural lemmas for Light Ternary Lookup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryLookup.lean

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCell
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightTernaryLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def body (pSearch pCell : ℕ) : Stmt :=
  .call pSearch [v 0,v 1,v 5,v 2,v 3,k 0] 9 ;;
  .call pSearch [v 0,v 1,v 6,v 2,v 3,k 0] 10 ;;
  .call pSearch [v 0,v 1,v 7,v 2,v 3,k 0] 11 ;;
  .call pCell [v 4,v 8 +' v 9 -' k 1,v 8 +' v 10 -' k 1,
    v 8 +' v 11 -' k 1] 0
def time (L : ℕ) : ℕ := 3 * LightBandLookup.searchTime L +
  LightTernaryCell.time + 150
def program : Program := [body 1 2, LightBandLookup.searchBody 1,
  LightTernaryCell.zetaBody]
end ThreeSum.LightTernaryLookup


