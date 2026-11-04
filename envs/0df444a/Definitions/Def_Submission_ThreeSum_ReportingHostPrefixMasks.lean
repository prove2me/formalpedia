-- Prove2me | Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
-- name    : Submission_ThreeSum_ReportingHostPrefixMasks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:51:16.361381+00:00
-- url     : https://prove2.me/theorems/a24248f7-f058-4fa1-b62f-eb32dc56b978
-- title:
--   Reporting Host Prefix Masks
-- statement:
--   Definitions and structural lemmas for Reporting Host Prefix Masks, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean

import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_pairs_mem

set_option autoImplicit false
namespace ThreeSum.ReportingHostPrefixMasks
open Finset ThreeSum.SubsetAddress BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open BlockForced
open ReportingHostPrefixCatalog ReportingHostPairEnumeration
open scoped BigOperators
set_option maxHeartbeats 500000
variable {α : Type*}
def tuple {h k : ℕ} (p : Prefix h k) : List (Finset (Fin (512*h)) × Finset (Fin (512*h))) :=
  List.ofFn fun i => (p i).val
def ofTuple {h k : ℕ} (xs : List (Finset (Fin (512*h)) × Finset (Fin (512*h))))
    (hlen : xs.length = k) (hmem : ∀ q ∈ xs, q ∈ pairs (512*h) h) : Prefix h k :=
  fun i => ⟨xs[i.val]'(by rw [hlen]; exact i.isLt),
    (pairs_mem _).mp (hmem _ (List.getElem_mem (by rw [hlen]; exact i.isLt)))⟩
end ThreeSum.ReportingHostPrefixMasks


