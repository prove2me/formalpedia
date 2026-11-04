-- Prove2me | Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
-- name    : Submission_ThreeSum_ReportingHostPackedCatalog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:00:56.027196+00:00
-- url     : https://prove2.me/theorems/9b1bbcc6-93a7-4b61-98db-6c92a20ba717
-- title:
--   Reporting Host Packed Catalog
-- statement:
--   Definitions and structural lemmas for Reporting Host Packed Catalog, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPackedCatalog.lean

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
set_option autoImplicit false
namespace ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000
def pairKey (radix left right : ℕ) : ℕ := left+radix*right
def packed (key : ℕ → ℕ) (n i : ℕ) : ℕ := key i*(n+1)+i
def codes (key : ℕ → ℕ) (n : ℕ) : List ℤ := List.ofFn fun i : Fin n => (packed key n i.val : ℤ)
def prefixKey (h J k i : ℕ) : ℕ :=
  pairKey (2^(J*(512*h))) (subsetMask (preL h J k i)) (subsetMask (preR h J k i))
end ThreeSum.ReportingHostPackedCatalog


