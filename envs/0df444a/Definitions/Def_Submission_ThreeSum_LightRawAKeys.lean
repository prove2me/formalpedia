-- Prove2me | Definitions.Def_Submission_ThreeSum_LightRawAKeys
-- name    : Submission_ThreeSum_LightRawAKeys
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:52:26.679289+00:00
-- url     : https://prove2.me/theorems/b471a3cf-2548-453e-9d71-42f642c83522
-- title:
--   Light Raw AKeys
-- statement:
--   Definitions and structural lemmas for Light Raw AKeys, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRawAKeys.lean

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightRawAKeys
open Light LightResidues RawIncidences RawAKeyLists
set_option maxHeartbeats 1000000
set_option maxRecDepth 6000
def body (pResidues pAffine : ℕ) : Stmt :=
  .set 4 (v 3 +' k 3 *' v 1) ;;
  .call pResidues [v 0,v 3 +' v 1,v 1,v 2,v 4,k 1] 5 ;;
  .call pAffine [v 3 +' v 1,v 3,v 1,k 0 -' v 2,k 1] 5 ;;
  .call pAffine [v 3 +' v 1,v 3 +' k 2 *' v 1,v 1,v 2,k 1] 5 ;;
  .set 0 (v 3)
def time (n U : ℕ) : ℕ := residuesTime n U+2*LightReportingAffine.time n+150
def space (free n U : ℕ) : ℕ := free+3*n+Nat.log 2 (U+1)+2
def word (p U : ℕ) : ℕ := 4*U+4*p+16
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1 2,residuesBody 3,LightReportingAffine.body,emodBody]
end ThreeSum.LightRawAKeys


