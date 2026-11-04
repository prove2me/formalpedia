-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
-- name    : Submission_ThreeSum_LightReportingSortedCatalog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:07:07.320467+00:00
-- url     : https://prove2.me/theorems/67f9bfed-5e3d-4a68-a6e1-0e0109142ca0
-- title:
--   Light Reporting Sorted Catalog
-- statement:
--   Definitions and structural lemmas for Light Reporting Sorted Catalog, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSortedCatalog.lean

import Definitions.Def_Submission_ThreeSum_LightReportingPackKeys
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightReportingSortedCatalog
open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog
variable {lim : Limits}
def body (pPowers pPack pSort : ℕ) : Stmt :=
  .call pPowers [v 5,v 0 +' k 1,k 2] 6 ;;
  .set 7 (M (v 5 +' v 0)) ;;
  .call pPack [v 1,v 2,v 3,v 7,v 4] 8 ;;
  .call pSort [v 3,v 4,v 5] 0
def program : Program :=
  [powTableBody,LightReportingPackKeys.body,sortBody 2 3 4 5,halfBody,mergeBody,copyBody,body 0 1 2]
def time (W n : ℕ) : ℕ := powTableTime (W+1)+LightReportingPackKeys.time n+sortTime n+120
def word (W n : ℕ) : ℕ := LightReportingPackKeys.word (2^W) n+2^(W+1)
end ThreeSum.LightReportingSortedCatalog


