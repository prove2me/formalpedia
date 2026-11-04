-- Prove2me | Definitions.Def_Submission_ThreeSum_LightPrimeCoefficient
-- name    : Submission_ThreeSum_LightPrimeCoefficient
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:39:02.722194+00:00
-- url     : https://prove2.me/theorems/a933ecfa-39dd-47f6-bd2f-57ca05c6a174
-- title:
--   Light Prime Coefficient
-- statement:
--   Definitions and structural lemmas for Light Prime Coefficient, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeCoefficient.lean

import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightPrimeCoefficient
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
def mulAddBody (pDivide : ℕ) : Stmt :=
  .call pDivide [v 0 +' v 1 *' v 2,v 3] 4 ;;
  .set 0 (v 0 +' v 1 *' v 2 -' v 4 *' v 3)
def word (p : ℕ) : ℕ := 4*(p+1)^2
def mulAddTime (p : ℕ) : ℕ := 20*(p+1)^2+100
end ThreeSum.LightPrimeCoefficient


