-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBruteThreeSum
-- name    : Submission_ThreeSum_LightBruteThreeSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:54:07.734471+00:00
-- url     : https://prove2.me/theorems/e18d67bf-c719-416f-b88e-ac534f867673
-- title:
--   Light Brute Three Sum
-- statement:
--   Definitions and structural lemmas for Light Brute Three Sum, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBruteThreeSum.lean

import Definitions.Def_Submission_ThreeSum_LightOriginalTripleScan
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightBruteThreeSum
open Light ThreeSumApsp.Spec
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
def body (pScan : ℕ) : Stmt :=
  .set 4 (v 0 *' v 0 *' v 0) ;;
  .call pScan [v 2,v 0,v 4] 0
def time (n : ℕ) : ℕ := LightOriginalTripleScan.time n (n^3)+100
def need (n U : ℕ) : Need :=
  ⟨LightOriginalTripleRow.word n U,0,n^3+3⟩
def program : Program := LightOriginalTripleScan.program ++ [body 2]
variable {lim : Limits} {P : Program}
end ThreeSum.LightBruteThreeSum


