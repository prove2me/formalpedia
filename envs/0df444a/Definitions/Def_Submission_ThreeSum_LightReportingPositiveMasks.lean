-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingPositiveMasks
-- name    : Submission_ThreeSum_LightReportingPositiveMasks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:43:18.657408+00:00
-- url     : https://prove2.me/theorems/e1806b97-6593-4c0a-bb58-b3d2da8ec3cd
-- title:
--   Light Reporting Positive Masks
-- statement:
--   Definitions and structural lemmas for Light Reporting Positive Masks, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPositiveMasks.lean

import Definitions.Def_Submission_ThreeSum_LightReportingGatherPair
import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
set_option autoImplicit false
namespace ThreeSum.LightReportingPositiveMasks
open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndexedQuery BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostPositive
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
def selectedIndices {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k < J) : List ℕ :=
  LightReportingFilter.selected (fun i => prefixQuery I w (k+1) (childAt w.2.2 pre hk i)) (groupSize h)
end ThreeSum.LightReportingPositiveMasks


