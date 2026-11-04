-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandWeightedScoreSlice
-- name    : Submission_ThreeSum_LightBandWeightedScoreSlice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:19:37.895791+00:00
-- url     : https://prove2.me/theorems/6c8ecf44-ecd3-4be1-a481-1f318d0d665c
-- title:
--   Light Band Weighted Score Slice
-- statement:
--   Definitions and structural lemmas for Light Band Weighted Score Slice, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandWeightedScoreSlice.lean

import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
namespace ThreeSum.LightBandWeightedScoreSlice
open Light
set_option maxHeartbeats 900000
def body : Stmt :=
  .set 3 (v 2 *' v 1) ;;
  .set 4 (v 0 -' v 3) ;;
  .ite (v 1 <' v 4) (.set 4 (v 1)) .skip ;;
  .set 0 (v 4)
def time : ℕ := 80
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
def program : Program := [body]
end ThreeSum.LightBandWeightedScoreSlice


