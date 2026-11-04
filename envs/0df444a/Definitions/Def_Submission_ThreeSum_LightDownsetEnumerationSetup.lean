-- Prove2me | Definitions.Def_Submission_ThreeSum_LightDownsetEnumerationSetup
-- name    : Submission_ThreeSum_LightDownsetEnumerationSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:36:15.781343+00:00
-- url     : https://prove2.me/theorems/79b73d9a-bb74-45e8-9bdc-23108f8646c4
-- title:
--   Light Downset Enumeration Setup
-- statement:
--   Definitions and structural lemmas for Light Downset Enumeration Setup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumerationSetup.lean

import Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightDownsetEnumerationSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def body (pPowers pDownset : ℕ) : Stmt :=
  .call pPowers [v 3,v 0 +' k 1,k 2] 4 ;;
  .call pDownset [v 0,v 1,v 2,v 3] 0
def time (L cut : ℕ) : ℕ := powTableTime (L+1)+LightDownsetEnumeration.time L cut+40
def program : Program :=
  [body 1 2,powTableBody,LightDownsetEnumeration.body 3,LightSubsetEnumeration.body 3]
end ThreeSum.LightDownsetEnumerationSetup


