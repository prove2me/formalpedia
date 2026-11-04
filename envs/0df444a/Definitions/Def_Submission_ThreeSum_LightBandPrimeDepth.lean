-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandPrimeDepth
-- name    : Submission_ThreeSum_LightBandPrimeDepth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:54:30.310958+00:00
-- url     : https://prove2.me/theorems/84f1b650-2166-454b-a426-87fa87199a72
-- title:
--   Light Band Prime Depth
-- statement:
--   Definitions and structural lemmas for Light Band Prime Depth, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeDepth.lean

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightBandPrimeDepth
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
def depth (R y : ℕ) : ℕ := Nat.log (4*y) (R/4)
def body : Stmt :=
  .set 2 (k 0) ;;
  .set 3 (k 16 *' v 1) ;;
  .while (v 3 ≤' v 0) (
    .set 3 (k 4 *' v 1 *' v 3) ;;
    .set 2 (v 2 +' k 1)) ;;
  .set 0 (v 2)
def time (R y : ℕ) : ℕ := 30*depth R y+30
def word (R y : ℕ) : ℕ := 4*y*(R+4)+R+8
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {R y : ℕ}
def program : Program := [body]
end ThreeSum.LightBandPrimeDepth


