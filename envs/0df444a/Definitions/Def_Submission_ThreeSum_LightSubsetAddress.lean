-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSubsetAddress
-- name    : Submission_ThreeSum_LightSubsetAddress
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:23:55.65664+00:00
-- url     : https://prove2.me/theorems/c924bc85-678b-4edc-aefb-380060e5fc8c
-- title:
--   Light Subset Address
-- statement:
--   Definitions and structural lemmas for Light Subset Address, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetAddress.lean

import Definitions.Def_Submission_ThreeSum_LightPascal
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSubsetAddress
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal
variable {lim : Limits} {P : Program}
def Powers (μ : ℕ → ℤ) (base W : ℕ) : Prop :=
  ∀ i ≤ W, μ (base+i) = ((2^i : ℕ) : ℤ)
def rankBody (pSelf : ℕ) : Stmt :=
  .ite (k 0 <' v 0)
    (.set 6 (v 0 -' k 1) ;;
      .ite (v 2 <' M (v 5 +' v 6))
        (.call pSelf [v 6,v 1,v 2,v 3,v 4,v 5] 0)
        (.call pSelf [v 6,v 1 -' k 1,v 2 -' M (v 5 +' v 6),v 3,v 4,v 5] 0 ;;
          .set 0 (v 0 +' M (v 4 +' v 6 *' (v 3 +' k 1) +' v 1))))
    (.set 0 (k 0))
def rankTime (L : ℕ) : ℕ := 100*L+30
def rankProgram : Program := [rankBody 0]
end ThreeSum.LightSubsetAddress


