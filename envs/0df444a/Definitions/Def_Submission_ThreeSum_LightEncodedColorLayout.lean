-- Prove2me | Definitions.Def_Submission_ThreeSum_LightEncodedColorLayout
-- name    : Submission_ThreeSum_LightEncodedColorLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:53:51.414414+00:00
-- url     : https://prove2.me/theorems/460412b5-4440-4a70-81ed-0f34e21c802f
-- title:
--   Light Encoded Color Layout
-- statement:
--   Definitions and structural lemmas for Light Encoded Color Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorLayout.lean

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
namespace ThreeSum.LightEncodedColorLayout
open Light BandPartition EncodedColorLayout
set_option maxHeartbeats 2200000
set_option maxRecDepth 11000
def body (pDivide : ℕ) : Stmt :=
  .call pDivide [v 0 -' k 1,v 1] 3 ;;
  .set 4 (v 3 +' k 1) ;;
  .set 5 (k 3 *' v 4 *' v 4) ;;
  .set 6 (v 2 +' k 8) ;;
  .set 7 (v 6 +' v 0) ;;
  .set 8 (v 7 +' v 0 +' k 1) ;;
  .set 9 (v 8 +' v 0 +' k 1) ;;
  .set 10 (v 9 +' v 0 +' k 1) ;;
  .set 11 (v 10 +' v 0) ;;
  .set 12 (v 11 +' k 2 +' k 2 *' v 0) ;;
  .set 13 (v 12 +' v 0) ;;
  .set 14 (v 13 +' k 2 +' k 2 *' v 0) ;;
  .set 15 (v 14 +' v 0) ;;
  .set 16 (v 15 +' k 2 +' k 2 *' v 0) ;;
  .set 17 (v 16 +' v 5) ;;
  .set 18 (v 17 +' k 4 *' v 5) ;;
  .set 19 (v 18 +' k 3 *' v 1 *' v 5) ;;
  .store (v 2) (v 10) ;;
  .store (v 2 +' k 1) (v 11) ;;
  .store (v 2 +' k 2) (v 12) ;;
  .store (v 2 +' k 3) (v 13) ;;
  .store (v 2 +' k 4) (v 14) ;;
  .store (v 2 +' k 5) (v 15) ;;
  .store (v 2 +' k 6) (v 17) ;;
  .store (v 2 +' k 7) (v 18) ;;
  .set 0 (v 19)
def time (n g : ℕ) : ℕ := LightSmallDivide.time (n-1) g+1000
def word (n g : ℕ) : ℕ := n+g+ColorBandBounds.count n g+100
noncomputable def headMemory (μ : ℕ → ℤ) (free n g : ℕ) : ℕ → ℤ :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update μ free (av free n))
      (free+1) (ae free n)) (free+2) (bv free n)) (free+3) (be free n))
      (free+4) (cv free n)) (free+5) (ce free n)) (free+6) (rec free n g)) (free+7) (vals free n g)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program := [body 1,LightSmallDivide.body]
end ThreeSum.LightEncodedColorLayout


