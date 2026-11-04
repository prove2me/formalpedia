-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
-- name    : Submission_ThreeSum_LightSubsetEnumerationSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:29:48.803064+00:00
-- url     : https://prove2.me/theorems/cac1c846-3382-4d6a-b432-a38ceca91ee8
-- title:
--   Light Subset Enumeration Setup
-- statement:
--   Definitions and structural lemmas for Light Subset Enumeration Setup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetEnumerationSetup.lean

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSubsetEnumerationSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def body (pPowers pEnum : ℕ) : Stmt :=
  .call pPowers [v 3,v 0 +' k 1,k 2] 4 ;;
  .call pEnum [v 0,v 1,k 0,v 2,v 3] 0
def time (L k : ℕ) : ℕ := powTableTime (L+1)+LightSubsetEnumeration.time L k+40
def program : Program := [body 1 2,powTableBody,LightSubsetEnumeration.body 2]
end ThreeSum.LightSubsetEnumerationSetup


