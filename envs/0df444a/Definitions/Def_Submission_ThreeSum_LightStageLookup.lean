-- Prove2me | Definitions.Def_Submission_ThreeSum_LightStageLookup
-- name    : Submission_ThreeSum_LightStageLookup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:41:58.729797+00:00
-- url     : https://prove2.me/theorems/4db4d680-2d5a-4f91-934d-e8b0128aff3a
-- title:
--   Light Stage Lookup
-- statement:
--   Definitions and structural lemmas for Light Stage Lookup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightStageLookup.lean

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages
import Definitions.Def_Submission_ThreeSum_LightDownsetAddress
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightStageLookup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def readAddr {L : ℕ} (cut base j : ℕ) (S : Finset (Fin L)) : ℕ :=
  base+j*downsetCap L cut+subsetRank S
def body (pSize pAddress : ℕ) : Stmt :=
  .call pSize [v 0,v 1,v 6] 7 ;;
  .call pAddress [v 0,v 2,v 3,v 6] 8 ;;
  .set 0 (M (v 5 +' v 4 *' v 7 +' v 8))
def time (L : ℕ) : ℕ := LightDownsetSize.time L+LightDownsetAddress.time L+50
def program : Program :=
  [body 1 2,LightDownsetSize.body 3 10,LightDownsetAddress.body 3 10,
    LightSubsetSetup.body 4 8 9,buildBody 5 6,fillBody,rowBody 7,
    LightArray.linearBody,powTableBody,rankBody 9,LightSubsetOffset.body]
end ThreeSum.LightStageLookup


