-- Prove2me | Definitions.Def_Submission_ThreeSum_ReportingHostPositiveBatch
-- name    : Submission_ThreeSum_ReportingHostPositiveBatch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:43:24.70004+00:00
-- url     : https://prove2.me/theorems/40c3e997-4c24-4038-860b-9b03c9e0b0d7
-- title:
--   Reporting Host Positive Batch
-- statement:
--   Definitions and structural lemmas for Reporting Host Positive Batch, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPositiveBatch.lean

import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
set_option autoImplicit false
namespace ThreeSum.ReportingHostPositiveBatch
open Finset BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostPositive
set_option linter.unusedSectionVars false
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
def parentAt {h : ℕ} (pres : List (List (Finset (Fin (512*h))))) (i : ℕ) := pres[i]?.getD []
def through {h J k : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (pres : List (List (Finset (Fin (512*h))))) (hk : k < J) (j : ℕ) :
    List (List (Finset (Fin (512*h)))) :=
  (pres.take j).flatMap (fun pre => positiveChildren I w pre hk)
end ThreeSum.ReportingHostPositiveBatch


