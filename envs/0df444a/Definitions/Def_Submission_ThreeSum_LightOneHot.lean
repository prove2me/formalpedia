-- Prove2me | Definitions.Def_Submission_ThreeSum_LightOneHot
-- name    : Submission_ThreeSum_LightOneHot
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:26:37.405203+00:00
-- url     : https://prove2.me/theorems/ab3913dd-d744-43e2-8dda-7303168616fa
-- title:
--   Light One Hot
-- statement:
--   Definitions and structural lemmas for Light One Hot, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOneHot.lean

import Definitions.Def_Submission_ThreeSum_OneHotMask
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightOneHot
open Light ThreeSum.OneHotMask ThreeSum.LightSubsetAddress
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : Limits} {P : Program}
def body (pSelf : ℕ) : Stmt :=
  .ite (k 0 <' v 0)
    (.set 6 (v 0 -' k 1) ;;
      .ite (v 1 <' M (v 3 +' v 6))
        (.call pSelf [v 6,v 1,v 2,v 3,v 4,v 5] 0 ;;
          .set 0 (v 0 +' M (v 4 +' v 6)))
        (.call pSelf [v 6,v 1 -' M (v 3 +' v 6),v 2,v 3,v 4,v 5] 0 ;;
          .set 0 (v 0 +' M (v 5 +' v 6))))
    (.set 0 (k 0))
def time (L : ℕ) : ℕ := 100*L+30
def word (W U : ℕ) : ℕ := 2^(W+1)+(W+1)*U
def setupBody (pPowers pHash : ℕ) : Stmt :=
  .call pPowers [v 4,v 0 +' k 1,k 2] 5 ;;
  .call pHash [v 0,v 1,v 0,v 4,v 2,v 3] 0
def setupTime (L : ℕ) : ℕ := powTableTime (L+1)+time L+40
def program : Program := [setupBody 1 2,powTableBody,body 2]
end ThreeSum.LightOneHot


