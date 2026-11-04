-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQuery
-- name    : Submission_ThreeSum_LightTernaryFrozenQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:37:15.93741+00:00
-- url     : https://prove2.me/theorems/8025aa34-fe97-44b0-a2a4-c3ee7216cae8
-- title:
--   Light Ternary Frozen Query
-- statement:
--   Definitions and structural lemmas for Light Ternary Frozen Query, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQuery.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightTernaryFrozenQuery
open Light
def childArgs (code rankDrop : Expr) : List Expr :=
  [v 0,v 16,v 2 -' rankDrop,v 3,code,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12]
def body (pSelf pLookup pDigit pZero pErase : ℕ) : Stmt :=
  .ite (v 2 ≤' v 3)
    (.call pLookup [v 5,v 6,v 4,v 7,v 11,v 12,v 1] 0)
    (.ite (v 1 =' k 0)
      (.call pLookup [v 8,v 9,v 4,v 10,v 11,v 12,k 0] 0)
      (.set 16 (v 1 -' k 1) ;;
        .call pDigit [k 2 *' v 0,k 2 *' (v 0 -' v 1),
          k 2 *' (v 0 -' v 1) +' k 1,v 4,v 11] 13 ;;
        .call pZero [k 2 *' v 0,k 2 *' (v 0 -' v 1),
          k 2 *' (v 0 -' v 1) +' k 1,v 4,v 11] 14 ;;
        .call pErase [k 2 *' v 0,k 2 *' (v 0 -' v 1) +' k 1,
          v 4,k 2 *' v 0,v 11] 15 ;;
        .ite (v 13 =' k 0)
          (.call pSelf (childArgs (v 14) (k 0)) 0)
          (.ite (v 13 =' k 1)
            (.call pSelf (childArgs (v 14) (k 1)) 18 ;;
              .call pSelf (childArgs (v 15) (k 0)) 19 ;;
              .set 0 (v 19 -' v 18))
            (.call pSelf (childArgs (v 14) (k 2)) 18 ;;
              .call pSelf (childArgs (v 15) (k 1)) 19 ;;
              .call pSelf (childArgs (v 4) (k 0)) 20 ;;
              .set 0 (v 20 -' k 2 *' v 19 +' v 18)))))
def program : Program :=
  [body 0 1 3 4 5,LightTernaryQueryLookup.body 2,
    LightBandLookup.searchBody 2,LightTernaryCodes.digitBody 5,
    LightTernaryCodes.zeroBody 5,LightMaskErase.body 5]
def inputs (N K rank cut : ℕ) (code : ℤ)
    (bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ) : List ℤ :=
  [N,K,rank,cut,code,bankCodes,bankCount,bankValues,nearCodes,nearCount,nearValues,powers,L]
variable {lim : Limits} {P : Program}
end ThreeSum.LightTernaryFrozenQuery


