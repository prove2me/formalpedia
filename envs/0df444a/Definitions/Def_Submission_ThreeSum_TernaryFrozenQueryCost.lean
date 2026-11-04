-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
-- name    : Submission_ThreeSum_TernaryFrozenQueryCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:08:48.841759+00:00
-- url     : https://prove2.me/theorems/a79fe0a6-78ba-4dac-804e-79ecd41ee414
-- title:
--   Ternary Frozen Query Cost
-- statement:
--   Definitions and structural lemmas for Ternary Frozen Query Cost, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits


set_option autoImplicit false
namespace ThreeSum.TernaryFrozenQueryCost
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
set_option maxHeartbeats 2000000
def caps {N : ℕ} (coords : List (Fin N)) (R : TritWord N) : List ℕ :=
  coords.map (fun i => (R i).val)
def work {N : ℕ} (T : ℕ) : List (Fin N)→TritWord N→ℕ
  | [], _ => 1
  | i::rest, R => if rank R≤T then 1 else
      1+∑ d : Fin 3, if d≤R i then work T rest (Function.update R i d) else 0
theorem caps_digits {N : ℕ} (coords : List (Fin N)) (R : TritWord N) :
    ∀ d∈caps coords R, d<3 := by
  intro d hd
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hd
  exact (R i).isLt
def capWord {N : ℕ} (coords : List (Fin N)) (R : TritWord N) : TritWord coords.length :=
  TernaryBankEnumeration.fromList (caps coords R) (by simp [caps]) (caps_digits coords R)
end ThreeSum.TernaryFrozenQueryCost


