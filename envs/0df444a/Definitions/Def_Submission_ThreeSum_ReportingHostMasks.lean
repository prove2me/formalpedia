-- Prove2me | Definitions.Def_Submission_ThreeSum_ReportingHostMasks
-- name    : Submission_ThreeSum_ReportingHostMasks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:47:52.675804+00:00
-- url     : https://prove2.me/theorems/a91ca70b-2eaa-4ade-a48b-95d5add5cd6e
-- title:
--   Reporting Host Masks
-- statement:
--   Definitions and structural lemmas for Reporting Host Masks, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean

import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
set_option autoImplicit false
namespace ThreeSum.ReportingHostMasks
open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced
def blockSet {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) : Finset (Fin (J*L)) :=
  indexSet (join {i} (fun _ => S))
def localRow {J L : ℕ} (i : Fin J) (T : Finset (Fin (J*L))) : Finset (Fin L) :=
  row (unindexSet T) i
def globalChildren {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :=
  QueryCoordinates.missingSets (blockSet i Q) h
def localChildren {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :=
  (globalChildren i Q h).map (localRow i)
end ThreeSum.ReportingHostMasks


