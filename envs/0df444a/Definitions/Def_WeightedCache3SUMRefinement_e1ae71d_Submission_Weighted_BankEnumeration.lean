-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:06:43.314502+00:00
-- url     : https://prove2.me/theorems/4125b913-25c4-46dc-b5b5-a4245d7f3256
-- title:
--   BankEnumeration
-- statement:
--   Definitions and structural lemmas for BankEnumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankEnumeration.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType
def bank (N T : ℕ) := WeightedCache.bank N ![0,1369,2740] T
def cacheCost {N : ℕ} (R : TritWord N) := WeightedCache.cost ![0,1369,2740] R
def wordList {N : ℕ} (w : TritWord N) : List ℕ := List.ofFn (fun i => (w i).val)
def fromList {N : ℕ} (xs : List ℕ) (hlen : xs.length = N)
    (hdigits : ∀ d ∈ xs, d < 3) : TritWord N := fun i =>
  ⟨xs[i.val]'(by omega), hdigits _ (List.getElem_mem (by omega))⟩
end ThreeSum.WeightedBankEnumeration
end WeightedCache3SUMRefinement_e1ae71d


