-- Prove2me | Definitions.Def_Submission_ThreeSum_LightDownsetSize
-- name    : Submission_ThreeSum_LightDownsetSize
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:29:40.138817+00:00
-- url     : https://prove2.me/theorems/59828ee8-2fcc-4c51-9312-fdf3f8c11577
-- title:
--   Light Downset Size
-- statement:
--   Definitions and structural lemmas for Light Downset Size, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetSize.lean

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightDownsetSize
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
def body (pSetup pOffset : ℕ) : Stmt :=
  .call pSetup [v 0,k 0,k 0,v 2] 3 ;;
  .call pOffset [v 2,v 0,v 1,v 0] 4 ;;
  .set 0 (v 4 +' M (v 2 +' v 0 *' (v 0 +' k 1) +' v 1))
def time (L : ℕ) : ℕ := LightSubsetSetup.time L+LightSubsetOffset.time L+60
def program : Program :=
  [body 1 8,LightSubsetSetup.body 2 6 7,buildBody 3 4,fillBody,rowBody 5,
    LightArray.linearBody,powTableBody,rankBody 7,LightSubsetOffset.body]
end ThreeSum.LightDownsetSize


