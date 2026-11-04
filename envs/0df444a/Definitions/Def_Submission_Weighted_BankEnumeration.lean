-- Prove2me | Definitions.Def_Submission_Weighted_BankEnumeration
-- name    : Submission_Weighted_BankEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:33:53.918878+00:00
-- url     : https://prove2.me/theorems/06dcb917-62f5-4bc5-a7eb-f2f754adb9b4
-- title:
--   Bank Enumeration
-- statement:
--   Definitions and structural lemmas for Bank Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
set_option autoImplicit false
namespace ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType
def bank (N T : ℕ) := WeightedCache.bank N ![0,512,1025] T
def cacheCost {N : ℕ} (R : TritWord N) := WeightedCache.cost ![0,512,1025] R
def wordList {N : ℕ} (w : TritWord N) : List ℕ := List.ofFn (fun i => (w i).val)
def fromList {N : ℕ} (xs : List ℕ) (hlen : xs.length = N)
    (hdigits : ∀ d ∈ xs, d < 3) : TritWord N := fun i =>
  ⟨xs[i.val]'(by omega), hdigits _ (List.getElem_mem (by omega))⟩
end ThreeSum.WeightedBankEnumeration


