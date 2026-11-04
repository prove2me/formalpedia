-- Prove2me | Definitions.Def_Submission_ThreeSum_LightRadixKeys
-- name    : Submission_ThreeSum_LightRadixKeys
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:28:35.284493+00:00
-- url     : https://prove2.me/theorems/1b94966d-60a5-4b84-85e3-a5c854903fa3
-- title:
--   Light Radix Keys
-- statement:
--   Definitions and structural lemmas for Light Radix Keys, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixKeys.lean

import Definitions.Def_Submission_ThreeSum_LightRadixRows
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightRadixKeys
open Light RadixKeyLists
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
def offset (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => offset m j+1+m^j
def space (dst m j : ℕ) : ℕ := dst+offset m j+1+m^j
def word (p U j : ℕ) : ℕ := LightRadixRows.word p U (U*(p+1)^j)
def time (m : ℕ) : ℕ → ℕ
  | 0 => 50
  | j+1 => time m j+LightRadixRows.time m (m^j)+200
def body (pSelf pRows : ℕ) : Stmt :=
  .ite (k 0 <' v 2)
    (.call pSelf [v 0,v 1,v 2 -' k 1,v 3,v 4] 5 ;;
      .set 6 (M (v 5)) ;;
      .set 7 (v 5 +' k 1 +' v 6) ;;
      .store (v 7) (v 1 *' v 6) ;;
      .call pRows [v 0,v 5 +' k 1,v 7 +' k 1,v 1,v 6,v 3] 8 ;;
      .set 0 (v 7))
    (.store (v 4) (k 1) ;; .store (v 4 +' k 1) (k 0) ;; .set 0 (v 4))
variable {lim : Limits} {P : Program}
def program : Program := [body 0 1,LightRadixRows.body 2,LightReportingAffine.body]
end ThreeSum.LightRadixKeys


