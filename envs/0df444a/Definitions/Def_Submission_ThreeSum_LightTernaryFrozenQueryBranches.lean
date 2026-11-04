-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryBranches
-- name    : Submission_ThreeSum_LightTernaryFrozenQueryBranches
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:43:22.991193+00:00
-- url     : https://prove2.me/theorems/b5e45900-b8c3-4a3b-bf37-70841c575180
-- title:
--   Light Ternary Frozen Query Branches
-- statement:
--   Definitions and structural lemmas for Light Ternary Frozen Query Branches, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryBranches.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQuery
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryFrozenQuery
open Light ThreeSum.TernaryQuery
set_option maxHeartbeats 3000000
def branches (pSelf : ℕ) : Stmt :=
  .ite (v 13 =' k 0)
    (.call pSelf (childArgs (v 14) (k 0)) 0)
    (.ite (v 13 =' k 1)
      (.call pSelf (childArgs (v 14) (k 1)) 18 ;;
        .call pSelf (childArgs (v 15) (k 0)) 19 ;;
        .set 0 (v 19 -' v 18))
      (.call pSelf (childArgs (v 14) (k 2)) 18 ;;
        .call pSelf (childArgs (v 15) (k 1)) 19 ;;
        .call pSelf (childArgs (v 4) (k 0)) 20 ;;
        .set 0 (v 20 -' k 2 *' v 19 +' v 18)))
def preparedInputs (N K rank cut : ℕ) (code : ℤ)
    (bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ)
    (q : Fin 3) (c0 c1 : ℤ) : List ℤ :=
  inputs N (K+1) rank cut code bankCodes bankCount bankValues nearCodes nearCount nearValues powers L ++
    [(q.val : ℤ),c0,c1,(K : ℤ)]
variable {lim : Limits} {P : Program}
end ThreeSum.LightTernaryFrozenQuery


