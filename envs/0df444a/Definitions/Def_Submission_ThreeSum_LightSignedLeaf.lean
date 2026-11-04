-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSignedLeaf
-- name    : Submission_ThreeSum_LightSignedLeaf
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:49:31.123861+00:00
-- url     : https://prove2.me/theorems/1dfad91d-30a4-42ff-ae4b-f55e6d1a9b17
-- title:
--   Light Signed Leaf
-- statement:
--   Definitions and structural lemmas for Light Signed Leaf, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeaf.lean

import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Definitions.Def_Submission_ThreeSum_LightStageLookup
import Definitions.Def_Submission_ThreeSum_LightSign
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSignedLeaf
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def body (pLookup pSign : ℕ) : Stmt :=
  .call pLookup [v 0,v 1,v 3 +' v 7,v 4 +' v 8,v 2,v 9,v 11] 12 ;;
  .call pLookup [v 0,v 1,v 5 +' v 7,v 6 +' v 8,v 2,v 10,v 11] 13 ;;
  .set 14 (v 12 *' v 13) ;;
  .call pSign [v 14,v 7] 0
def time (W : ℕ) : ℕ := 2*LightStageLookup.time W+LightSign.time W+80
def program : Program :=
  [body 1 12,LightStageLookup.body 2 3,LightDownsetSize.body 4 11,
    LightDownsetAddress.body 4 11,LightSubsetSetup.body 5 9 10,
    buildBody 6 7,fillBody,rowBody 8,LightArray.linearBody,powTableBody,
    rankBody 10,LightSubsetOffset.body,LightSign.body]
end ThreeSum.LightSignedLeaf


