-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
-- name    : Submission_ThreeSum_LightReportingCatalogLookup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:04:51.041951+00:00
-- url     : https://prove2.me/theorems/7d2dcb44-1bf2-4341-85bc-6e2eee73c531
-- title:
--   Light Reporting Catalog Lookup
-- statement:
--   Definitions and structural lemmas for Light Reporting Catalog Lookup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogLookup.lean

import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightReportingCatalogLookup
open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog
set_option maxHeartbeats 1500000
set_option maxRecDepth 8000
variable {lim : Limits}
def valueBound (W n : ℕ) : ℕ := 2^(2*W)*(n+1)
def word (W n : ℕ) : ℕ :=
  4*valueBound W n+4*(n+1)+n+2^(2*W+2)+2^(W+1)+16
def body (pPowers pSearch pEmod : ℕ) : Stmt :=
  .call pPowers [v 5,k 2 *' v 0 +' k 2,k 2] 6 ;;
  .set 7 (M (v 5 +' v 0)) ;;
  .set 8 (((v 3 +' v 7 *' v 4) *' (v 1 +' k 1)) +' v 1) ;;
  .call pSearch [v 2,v 1,v 8,v 5,k 2 *' v 0 +' k 1,k 0] 9 ;;
  .set 10 (M (v 2 +' v 9 -' k 1)) ;;
  .call pEmod [v 10,v 1 +' k 1,v 5] 0
def program : Program := [powTableBody,LightBandLookup.searchBody 1,emodBody,body 0 1 2]
def time (W n : ℕ) : ℕ := powTableTime (2*W+2)+LightBandLookup.searchTime (2*W+1)+
  100*(Nat.log 2 (valueBound W n+1)+2)+200
end ThreeSum.LightReportingCatalogLookup


