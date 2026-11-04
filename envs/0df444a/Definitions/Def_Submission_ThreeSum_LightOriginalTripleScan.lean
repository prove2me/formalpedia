-- Prove2me | Definitions.Def_Submission_ThreeSum_LightOriginalTripleScan
-- name    : Submission_ThreeSum_LightOriginalTripleScan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:51:45.536196+00:00
-- url     : https://prove2.me/theorems/67e532d8-9eb0-4ed2-8120-4eef82fca343
-- title:
--   Light Original Triple Scan
-- statement:
--   Definitions and structural lemmas for Light Original Triple Scan, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalTripleScan.lean

import Definitions.Def_Submission_ThreeSum_LightOriginalTripleRow
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightOriginalTripleScan
open Light BruteTripleIndex
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
def body (pSelf pRow : ℕ) : Stmt :=
  .ite (k 0 <' v 2)
    (.call pSelf [v 0,v 1,v 2 -' k 1] 3 ;;
      .call pRow [v 0,v 1,v 2 -' k 1] 4 ;;
      .ite (k 0 <' v 3 +' v 4) (.set 0 (k 1)) (.set 0 (k 0)))
    (.set 0 (k 0))
def time (n t : ℕ) : ℕ := t*(LightOriginalTripleRow.time n+150)+50
variable {lim : Limits} {P : Program}
def program : Program := LightOriginalTripleRow.program ++ [body 2 0]
end ThreeSum.LightOriginalTripleScan


