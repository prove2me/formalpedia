-- Prove2me | Definitions.Def_Submission_Weighted_NearCanonical
-- name    : Submission_Weighted_NearCanonical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:06:49.364759+00:00
-- url     : https://prove2.me/theorems/ded04156-d44c-4baf-92f3-08dfc5736ee5
-- title:
--   Near Canonical
-- statement:
--   Definitions and structural lemmas for Near Canonical, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearCanonical.lean

import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_NearPair
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_digits
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_admitted_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_admitted_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_words
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_digits
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_words
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_admitted_digits
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_admitted_length
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_words
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length


set_option autoImplicit false
namespace ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
def word {N : ℕ} (Q : TritWord N) (D j : ℕ) : TritWord N :=
  if hj : j<(WeightedNearEnumeration.words (wordList Q) D).length then
    fromList (WeightedNearEnumeration.words (wordList Q) D)[j]
      ((WeightedNearEnumeration.admitted_length
        ((WeightedNearEnumeration.mem_words _ _ _).mp (List.getElem_mem hj))).trans (wordList_length Q))
      (WeightedNearEnumeration.admitted_digits (wordList_digits Q)
        ((WeightedNearEnumeration.mem_words _ _ _).mp (List.getElem_mem hj)))
  else fun _ => 0
end ThreeSum.WeightedNearCanonical


