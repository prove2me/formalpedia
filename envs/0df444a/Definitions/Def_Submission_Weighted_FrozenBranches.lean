-- Prove2me | Definitions.Def_Submission_Weighted_FrozenBranches
-- name    : Submission_Weighted_FrozenBranches
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:43:12.883332+00:00
-- url     : https://prove2.me/theorems/9f52ab55-ed74-44e8-b80c-03ff87912db4
-- title:
--   Frozen Branches
-- statement:
--   Definitions and structural lemmas for Frozen Branches, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenBranches.lean

import Definitions.Def_Submission_Weighted_Enumeration
import Definitions.Def_Submission_Weighted_Frozen
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightWeightedFrozenQuery
open Light ThreeSum.TernaryQuery
open ThreeSum.WeightedEnumeration (digitCost)
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
def branches (pSelf : ℕ) : Stmt :=
  .ite (v 13 =' k 0)
    (.call pSelf (childArgs (v 14) (k 0)) 0)
    (.ite (v 13 =' k 1)
      (.call pSelf (childArgs (v 14) (k 512)) 18 ;;
        .call pSelf (childArgs (v 15) (k 0)) 19 ;;
        .set 0 (v 19 -' v 18))
      (.call pSelf (childArgs (v 14) (k 1025)) 18 ;;
        .call pSelf (childArgs (v 15) (k 513)) 19 ;;
        .call pSelf (childArgs (v 4) (k 0)) 20 ;;
        .set 0 (v 20 -' k 2 *' v 19 +' v 18)))
def preparedInputs (N K rank cut : ℕ) (code : ℤ)
    (bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ)
    (q : Fin 3) (c0 c1 : ℤ) : List ℤ :=
  inputs N (K+1) rank cut code bankCodes bankCount bankValues nearCodes nearCount nearValues powers L ++
    [(q.val : ℤ),c0,c1,(K : ℤ)]
variable {lim : Limits} {P : Program}
end ThreeSum.LightWeightedFrozenQuery


