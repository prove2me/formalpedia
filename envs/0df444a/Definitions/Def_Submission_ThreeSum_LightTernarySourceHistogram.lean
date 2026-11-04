-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernarySourceHistogram
-- name    : Submission_ThreeSum_LightTernarySourceHistogram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:38:16.459225+00:00
-- url     : https://prove2.me/theorems/b371be1f-4ea4-4994-b4fb-3a4491849215
-- title:
--   Light Ternary Source Histogram
-- statement:
--   Definitions and structural lemmas for Light Ternary Source Histogram, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceHistogram.lean

import Definitions.Def_Submission_ThreeSum_LightTernarySourceKeys
import Theorems.Thm_Light_Ends_call
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e

set_option autoImplicit false
namespace ThreeSum.LightTernarySourceHistogram
open Light ThreeSum.LightArray ThreeSum.LightSubsetAddress
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {d : ℕ}
def scaleBody : Stmt :=
  pass 3 (v 1) (v 0) (v 2 *' M (v 0 +' v 3))
def scaleTime (n : ℕ) : ℕ := 20*n+10
def body (pKeys pHist pScale : ℕ) : Stmt :=
  .call pKeys [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8] 11 ;;
  .call pHist [v 8,v 9,v 5,v 1] 11 ;;
  .call pScale [v 9,v 1,v 10] 11
def time (L count bank : ℕ) : ℕ := LightTernarySourceKeys.time L count +
  LightHistogram.histogramTime count bank + scaleTime bank + 200
def program : Program := [body 1 3 5,LightTernarySourceKeys.body 2,
  LightBandLookup.searchBody 2,LightHistogram.histogramBody 4,fillBody,scaleBody]
end ThreeSum.LightTernarySourceHistogram


