-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
-- name    : Submission_ThreeSum_TernaryBankEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:34:23.961837+00:00
-- url     : https://prove2.me/theorems/5c722987-ddd0-445f-8ff0-e468e3356307
-- title:
--   Ternary Bank Enumeration
-- statement:
--   Definitions and structural lemmas for Ternary Bank Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
set_option autoImplicit false
namespace ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
def wordList {N : ℕ} (w : TritWord N) : List ℕ := List.ofFn (fun i => (w i).val)
def fromList {N : ℕ} (xs : List ℕ) (hlen : xs.length = N)
    (hdigits : ∀ d ∈ xs, d < 3) : TritWord N := fun i =>
  ⟨xs[i.val]'(by omega), hdigits _ (List.getElem_mem (by omega))⟩
end ThreeSum.TernaryBankEnumeration


