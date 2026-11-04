-- Prove2me | Definitions.Def_Submission_ThreeSum_ReportingHostPositive
-- name    : Submission_ThreeSum_ReportingHostPositive
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:39:00.339758+00:00
-- url     : https://prove2.me/theorems/06c0b01f-e9c1-497f-b6ab-3096037391dd
-- title:
--   Reporting Host Positive
-- statement:
--   Definitions and structural lemmas for Reporting Host Positive, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositive.lean

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogExpand
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
set_option autoImplicit false
namespace ThreeSum.ReportingHostPositive
open Light Finset ThreeSum.SubsetAddress
open BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostFrontier
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
def positiveChildren {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k < J) :
    List (List (Finset (Fin (512*h)))) :=
  (LightReportingFilter.selected (fun i => prefixQuery I w (k+1) (childAt w.2.2 pre hk i))
    (groupSize h)).map (childAt w.2.2 pre hk)
def parentWork {h J : ℕ} (I : Finset (RawItem h J α β γ)) (k t : ℕ) : ℕ :=
  ∑ w : Wanted h J α, (ReportingHostFrontier.frontier I w k).length*
    LightReportingCatalogExpand.time h J k t
end ThreeSum.ReportingHostPositive


