-- Prove2me | Definitions.Def_DeletionCode_GoodWordBridge
-- name    : DeletionCode_GoodWordBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:01:14.132066+00:00
-- url     : https://prove2.me/theorems/7464c606-8573-4839-8fa6-db106a88f8b3
-- title:
--   Good Word Bridge
-- statement:
--   Definitions and structural lemmas for Good Word Bridge, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GoodWordBridge.lean

import Definitions.Def_DeletionCode_CodeSelection
import Definitions.Def_DeletionCode_UniqueWordCount
import Definitions.Def_DeletionCode_ExceptionalProbability
import Definitions.Def_DeletionCode_ObstructionProbability
set_option autoImplicit true
namespace DeletionCode.GoodWordBridge
open Windows HeaderRecovery SignedSupport CircleHash ConflictGraphWitness
open ExceptionalProbability ObstructionProbability BipartiteSelection
variable {n : ℕ}
noncomputable def retainedWords (t k Q : ℕ) (weights : Gram (windowLength k) → ℝ) :
    Finset (Bits n) := by
  classical
  exact (UniqueWordCount.uniqueWords n k).filter (fun x =>
    weights ∉ exceptionalEvent t k Q x ∪ obstructionEvent t k Q x)
end DeletionCode.GoodWordBridge


