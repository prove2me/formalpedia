-- Prove2me | Definitions.Def_Submission_ThreeSum_LightColorScan
-- name    : Submission_ThreeSum_LightColorScan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:27:52.045316+00:00
-- url     : https://prove2.me/theorems/e3782803-7de7-46ee-8ae7-265c936ef46d
-- title:
--   Light Color Scan
-- statement:
--   Definitions and structural lemmas for Light Color Scan, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorScan.lean

import Definitions.Def_Submission_ThreeSum_ColorScan
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightColorScan
open Light ColorParameters ColorScan
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
def body (pSelf pParameters pColor : ℕ) : Stmt :=
  .ite (k 0 <' v 5)
    (.call pSelf [v 0,v 1,v 2,v 3,v 4,v 5 -' k 1] 6 ;;
      .ite (k 0 <' v 6)
        (.set 0 (k 1))
        (.set 7 (v 5 -' k 1) ;;
          .call pParameters [v 4,v 7,v 3] 8 ;;
          .call pColor [v 0,v 1,v 2,v 3,v 3 +' k 6] 9 ;;
          .set 0 (v 9)))
    (.set 0 (k 0))
def time (colorTime W t : ℕ) : ℕ :=
  t*(100*count W+colorTime+3000)+100
structure Procs (P : Program) (pMain : ℕ) where
  pParameters : ℕ
  pDivide : ℕ
  pColor : ℕ
  main : P[pMain]?=some (body pMain pParameters pColor)
  parameters : P[pParameters]?=some (LightColorParameters.body pDivide)
  divide : P[pDivide]?=some LightSmallDivide.body
variable {lim : Limits} {P : Program}
end ThreeSum.LightColorScan


