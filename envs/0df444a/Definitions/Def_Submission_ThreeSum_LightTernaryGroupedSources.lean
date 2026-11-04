-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSources
-- name    : Submission_ThreeSum_LightTernaryGroupedSources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:41:32.481196+00:00
-- url     : https://prove2.me/theorems/ce55906f-4c66-4cd1-b5f1-5409dd95a781
-- title:
--   Light Ternary Grouped Sources
-- statement:
--   Definitions and structural lemmas for Light Ternary Grouped Sources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupedSources.lean

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSourceKeys
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightTernaryGroupedSources
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program} {d : ℕ}
def body (pKeys pHist pScale : ℕ) : Stmt :=
  .call pKeys [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 13,v 14] 15 ;;
  .call pHist [v 8,v 4,v 10,v 5,v 9,v 1 *' v 14,v 11] 15 ;;
  .call pScale [v 9,v 1 *' v 14,v 12] 15
def time (L count bank groups : ℕ) : ℕ := LightTernaryGroupedSourceKeys.time L count+
  LightTernaryWeightedHistogram.time count (groups*bank)+
  LightTernarySourceHistogram.scaleTime (groups*bank)+250
def program : Program := [body 1 3 5,LightTernaryGroupedSourceKeys.body 2,
  LightBandLookup.searchBody 2,LightTernaryWeightedHistogram.body 4,
  fillBody,LightTernarySourceHistogram.scaleBody]
end ThreeSum.LightTernaryGroupedSources


