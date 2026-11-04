-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandPartition
-- name    : Submission_ThreeSum_LightBandPartition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:17:38.50939+00:00
-- url     : https://prove2.me/theorems/f197eca4-cffc-49f6-8622-c413ff030304
-- title:
--   Light Band Partition
-- statement:
--   Definitions and structural lemmas for Light Band Partition, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPartition.lean

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Theorems.Thm_Light_Ends_call
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightBandPartition
open Light ThreeSum.BandPartition
variable {lim : Limits} {P : Program}
def lowerBody : Stmt :=
  pass 4 (v 2) (v 1) (M (v 0 +' v 4 *' v 3))
def lowerTime (m : ℕ) : ℕ := 25*m+6
def upperBody : Stmt :=
  .for 5 (v 4) (
    .set 6 ((v 5 +' k 1) *' v 2) ;;
    .ite (v 1 <' v 6) (.set 6 (v 1)) .skip ;;
    .store (v 3 +' v 5) (M (v 0 +' v 6 -' k 1)))
def upperTime (m : ℕ) : ℕ := 100*m+6
def body (pDivide pLower pUpper : ℕ) : Stmt :=
  .ite (k 0 <' v 1)
    (.call pDivide [v 1 -' k 1,v 2] 4 ;;
      .set 4 (v 4 +' k 1) ;;
      .set 5 (v 3 +' v 1) ;;
      .call pLower [v 0,v 3,v 4,v 2] 6 ;;
      .call pUpper [v 0,v 1,v 2,v 5,v 4] 6 ;;
      .set 0 (v 4))
    (.set 0 (k 0))
def time (n g : ℕ) : ℕ :=
  LightSmallDivide.time (n-1) g+lowerTime (size n g)+upperTime (size n g)+100
def program : Program := [body 1 2 3,LightSmallDivide.body,lowerBody,upperBody]
end ThreeSum.LightBandPartition


