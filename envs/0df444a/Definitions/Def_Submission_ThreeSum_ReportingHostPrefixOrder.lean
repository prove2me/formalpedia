-- Prove2me | Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
-- name    : Submission_ThreeSum_ReportingHostPrefixOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:53:24.090526+00:00
-- url     : https://prove2.me/theorems/673f4ad4-6f06-4396-958b-5b2480fbfd19
-- title:
--   Reporting Host Prefix Order
-- statement:
--   Definitions and structural lemmas for Reporting Host Prefix Order, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixOrder.lean

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Theorems.Thm_ThreeSum_RadixKeyLists_mem_tuples

set_option autoImplicit false
namespace ThreeSum.ReportingHostPrefixOrder
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments
set_option maxHeartbeats 600000
def prefixes (h k : ℕ) : List (Prefix h k) :=
  (RadixKeyLists.tuples (pairs (512*h) h) k).attach.map fun t =>
    ofTuple t.val ((RadixKeyLists.mem_tuples _ _ _).mp t.property).1
      ((RadixKeyLists.mem_tuples _ _ _).mp t.property).2
def leftSets (h J k : ℕ) : List (Finset (Fin (J*(512*h)))) :=
  (prefixes h k).map (leftSet (J := J))
def rightSets (h J k : ℕ) : List (Finset (Fin (J*(512*h)))) :=
  (prefixes h k).map (rightSet (J := J))
def preL (h J k i : ℕ) : Finset (Fin (J*(512*h))) := ((leftSets h J k)[i]?).getD ∅
def preR (h J k i : ℕ) : Finset (Fin (J*(512*h))) := ((rightSets h J k)[i]?).getD ∅
end ThreeSum.ReportingHostPrefixOrder


