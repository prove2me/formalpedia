-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSubsetOffset
-- name    : Submission_ThreeSum_LightSubsetOffset
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:26:31.812896+00:00
-- url     : https://prove2.me/theorems/8bd2eb34-89ca-480c-bcdb-32086178b47e
-- title:
--   Light Subset Offset
-- statement:
--   Definitions and structural lemmas for Light Subset Offset, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetOffset.lean

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSubsetOffset
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program} {d : ℕ}
def body : Stmt :=
  .set 5 (k 0) ;;
  .for 4 (v 2) (
    .set 5 (v 5 +' M (v 0 +' v 1 *' (v 3 +' k 1) +' v 4))) ;;
  .set 0 (v 5)
def time (k : ℕ) : ℕ := 30*k+20
end ThreeSum.LightSubsetOffset


