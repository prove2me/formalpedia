-- Prove2me | Definitions.Def_Submission_ThreeSum_LightWantedJoin
-- name    : Submission_ThreeSum_LightWantedJoin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:59:51.707143+00:00
-- url     : https://prove2.me/theorems/1e3c0b03-07d0-4b47-99b2-15e0928d2421
-- title:
--   Light Wanted Join
-- statement:
--   Definitions and structural lemmas for Light Wanted Join, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedJoin.lean

import Definitions.Def_Submission_ThreeSum_LightWantedRow
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightWantedJoin
open Light SourceBuckets WantedPairs
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
def body (pSelf pRow : ℕ) : Stmt :=
  .ite (k 0 <' v 3)
    (.call pSelf [v 0,v 1,v 2,v 3 -' k 1,v 4,v 5,v 6] 7 ;;
      .set 8 (v 3 -' k 1) ;;
      .set 9 (M (v 0 +' v 8)) ;;
      .set 10 (M (v 1 +' v 9)) ;;
      .set 11 (M (v 1 +' v 9 +' k 1) -' v 10) ;;
      .call pRow [v 8,v 2,v 10,v 11,v 6,v 7] 12 ;;
      .set 0 (v 7 +' v 11))
    (.set 0 (k 0))
def time (left right : ℕ → ℕ) (NR : ℕ) : ℕ → ℕ
  | 0 => 50
  | n+1 => time left right NR n+LightWantedRow.time (LightHistogram.count right (left n) NR)+250
variable {lim : Limits} {P : Program}
def program : Program := [body 0 1,LightWantedRow.body]
end ThreeSum.LightWantedJoin


