-- Prove2me | Definitions.Def_Submission_ThreeSum_LightColorParameters
-- name    : Submission_ThreeSum_LightColorParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:45:55.432093+00:00
-- url     : https://prove2.me/theorems/2f9b36b4-cccc-4c5e-9d60-d41db6be6b77
-- title:
--   Light Color Parameters
-- statement:
--   Definitions and structural lemmas for Light Color Parameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorParameters.lean

import Definitions.Def_Submission_ThreeSum_ColorParameters
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightColorParameters
open Light ColorParameters
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
def body (pDivide : ℕ) : Stmt :=
  .call pDivide [v 1,k 3] 3 ;;
  .call pDivide [v 3,k 3] 4 ;;
  .call pDivide [v 4,k 3] 5 ;;
  .call pDivide [v 5,k 3] 6 ;;
  .call pDivide [v 6,v 0] 7 ;;
  .set 8 (v 6 -' v 7 *' v 0) ;;
  .set 9 (v 5 -' v 6 *' k 3) ;;
  .set 10 (v 4 -' v 5 *' k 3) ;;
  .set 11 (v 3 -' v 4 *' k 3) ;;
  .set 12 (v 1 -' v 3 *' k 3) ;;
  .store (v 2) (v 7) ;;
  .store (v 2 +' k 1) (v 8) ;;
  .store (v 2 +' k 2) (v 9) ;;
  .store (v 2 +' k 3) (v 10) ;;
  .store (v 2 +' k 4) (v 11) ;;
  .store (v 2 +' k 5) (v 12) ;;
  .set 0 (v 2)
def time (t : ℕ) : ℕ := 100*t+2000
variable {lim : Limits} {P : Program} {d W t free : ℕ} {μ : ℕ → ℤ}
def program : Program := [body 1,LightSmallDivide.body]
end ThreeSum.LightColorParameters


