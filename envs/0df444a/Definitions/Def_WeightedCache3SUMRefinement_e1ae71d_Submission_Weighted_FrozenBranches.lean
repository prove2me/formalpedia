-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenBranches
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenBranches
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:06:57.338183+00:00
-- url     : https://prove2.me/theorems/8c49f5b7-f8c0-4882-9a57-8458bb532d39
-- title:
--   FrozenBranches
-- statement:
--   Definitions and structural lemmas for FrozenBranches, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrozenBranches.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Frozen
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedFrozenQuery
open Light ThreeSum.TernaryQuery
open ThreeSum.WeightedEnumeration (digitCost)
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
def branches (pSelf : ℕ) : Stmt :=
  .ite (v 13 =' k 0)
    (.call pSelf (childArgs (v 14) (k 0)) 0)
    (.ite (v 13 =' k 1)
      (.call pSelf (childArgs (v 14) (k 1369)) 18 ;;
        .call pSelf (childArgs (v 15) (k 0)) 19 ;;
        .set 0 (v 19 -' v 18))
      (.call pSelf (childArgs (v 14) (k 2740)) 18 ;;
        .call pSelf (childArgs (v 15) (k 1371)) 19 ;;
        .call pSelf (childArgs (v 4) (k 0)) 20 ;;
        .set 0 (v 20 -' k 2 *' v 19 +' v 18)))
def preparedInputs (N K rank cut : ℕ) (code : ℤ)
    (bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ)
    (q : Fin 3) (c0 c1 : ℤ) : List ℤ :=
  inputs N (K+1) rank cut code bankCodes bankCount bankValues nearCodes nearCount nearValues powers L ++
    [(q.val : ℤ),c0,c1,(K : ℤ)]
variable {lim : Limits} {P : Program}
end ThreeSum.LightWeightedFrozenQuery
end WeightedCache3SUMRefinement_e1ae71d


