-- Prove2me | Definitions.Def_Submission_Weighted_EnumerationSetup
-- name    : Submission_Weighted_EnumerationSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:32:51.103786+00:00
-- url     : https://prove2.me/theorems/5c9003b7-08bd-4a60-9fa9-d28a8df2c20c
-- title:
--   Enumeration Setup
-- statement:
--   Definitions and structural lemmas for Enumeration Setup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/EnumerationSetup.lean

import Definitions.Def_Submission_Weighted_LightEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightWeightedEnumerationSetup
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
variable {lim : Limits} {P : Program}
def body (pPowers pEnum : ℕ) : Stmt :=
  .call pPowers [v 3,k 2 *' v 0 +' k 1,k 2] 4 ;;
  .call pEnum [v 0,v 1,k 0,v 2,v 3] 0
def time (N T : ℕ) : ℕ := powTableTime (2*N+1)+LightCacheEnumeration.time N T+40
def program : Program := [body 1 2,powTableBody,LightCacheEnumeration.body 2]
end ThreeSum.LightWeightedEnumerationSetup


