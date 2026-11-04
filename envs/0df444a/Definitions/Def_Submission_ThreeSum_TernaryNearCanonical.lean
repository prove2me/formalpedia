-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
-- name    : Submission_ThreeSum_TernaryNearCanonical
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:06:16.128058+00:00
-- url     : https://prove2.me/theorems/d1402de9-b978-485c-89b1-5a4b74378f4f
-- title:
--   Ternary Near Canonical
-- statement:
--   Definitions and structural lemmas for Ternary Near Canonical, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearCanonical.lean

import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_digits
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_admitted_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_admitted_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_words
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length


set_option autoImplicit false
namespace ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
def word {N : ℕ} (Q : TritWord N) (D j : ℕ) : TritWord N :=
  if hj : j<(TernaryNearEnumeration.words (wordList Q) D).length then
    fromList (TernaryNearEnumeration.words (wordList Q) D)[j]
      ((TernaryNearEnumeration.admitted_length
        ((TernaryNearEnumeration.mem_words _ _ _).mp (List.getElem_mem hj))).trans (wordList_length Q))
      (TernaryNearEnumeration.admitted_digits (wordList_digits Q)
        ((TernaryNearEnumeration.mem_words _ _ _).mp (List.getElem_mem hj)))
  else fun _ => 0
end ThreeSum.TernaryNearCanonical


