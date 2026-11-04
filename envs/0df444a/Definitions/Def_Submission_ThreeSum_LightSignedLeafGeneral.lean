-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSignedLeafGeneral
-- name    : Submission_ThreeSum_LightSignedLeafGeneral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:52:18.164192+00:00
-- url     : https://prove2.me/theorems/a649bae1-f643-4260-8a58-c2da9afdc856
-- title:
--   Light Signed Leaf General
-- statement:
--   Definitions and structural lemmas for Light Signed Leaf General, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedLeafGeneral.lean

import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Definitions.Def_Submission_ThreeSum_LightMaskUnion
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSignedLeafGeneral
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def body (pUnion pLookup pSign : ℕ) : Stmt :=
  .call pUnion [v 0,v 3,v 4,v 8,v 11,v 11 +' k 1] 12 ;;
  .set 13 (M (v 11)) ;;
  .call pLookup [v 0,v 1,v 13,v 12,v 2,v 9,v 11 +' k 1] 14 ;;
  .call pUnion [v 0,v 5,v 6,v 8,v 11,v 11 +' k 1] 15 ;;
  .set 16 (M (v 11)) ;;
  .call pLookup [v 0,v 1,v 16,v 15,v 2,v 10,v 11 +' k 1] 17 ;;
  .set 18 (v 14 *' v 17) ;;
  .call pSign [v 18,v 7] 0
def time (W : ℕ) : ℕ :=
  2*LightMaskUnion.time W+2*LightStageLookup.time W+LightSign.time W+160
def program : Program :=
  [body 1 2 14,LightMaskUnion.body 10 13,LightStageLookup.body 3 4,
    LightDownsetSize.body 5 12,LightDownsetAddress.body 5 12,
    LightSubsetSetup.body 6 10 11,buildBody 7 8,fillBody,rowBody 9,
    LightArray.linearBody,powTableBody,rankBody 11,LightSubsetOffset.body,
    LightMaskErase.body 13,LightSign.body]
end ThreeSum.LightSignedLeafGeneral


