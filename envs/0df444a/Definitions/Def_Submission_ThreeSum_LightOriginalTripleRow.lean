-- Prove2me | Definitions.Def_Submission_ThreeSum_LightOriginalTripleRow
-- name    : Submission_ThreeSum_LightOriginalTripleRow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:48:28.867471+00:00
-- url     : https://prove2.me/theorems/c2082bf9-5feb-417f-9605-c1a3825612ea
-- title:
--   Light Original Triple Row
-- statement:
--   Definitions and structural lemmas for Light Original Triple Row, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalTripleRow.lean

import Definitions.Def_Submission_ThreeSum_BruteTripleIndex
import Definitions.Def_Submission_ThreeSum_LightColorParameters
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightOriginalTripleRow
open Light BruteTripleIndex
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
def body (pDivide : ℕ) : Stmt :=
  .call pDivide [v 2,v 1] 3 ;;
  .call pDivide [v 3,v 1] 4 ;;
  .set 5 (v 3 -' v 4 *' v 1) ;;
  .set 6 (v 2 -' v 3 *' v 1) ;;
  .set 7 (M (v 0 +' v 4)) ;;
  .set 8 (M (v 0 +' v 5)) ;;
  .set 9 (M (v 0 +' v 6)) ;;
  .set 10 (v 7 +' v 8 +' v 9) ;;
  .ite (v 4 =' v 5) (.set 0 (k 0))
    (.ite (v 4 =' v 6) (.set 0 (k 0))
      (.ite (v 5 =' v 6) (.set 0 (k 0))
        (.ite (v 10 =' k 0) (.set 0 (k 1)) (.set 0 (k 0)))))
def time (n : ℕ) : ℕ := 20*(n*n+n)+500
def word (n U : ℕ) : ℕ := n^3+3*U+n+20
variable {lim : Limits} {P : Program}
def program : Program := [body 1,LightSmallDivide.body]
end ThreeSum.LightOriginalTripleRow


