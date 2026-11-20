-- Prove2me | Definitions.Def_DeletionCode_UniqueWordCount
-- name    : DeletionCode_UniqueWordCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:35:23.778694+00:00
-- url     : https://prove2.me/theorems/4567a6d6-cd08-445c-a68e-afd115f4f32b
-- title:
--   Unique Word Count
-- statement:
--   Definitions and structural lemmas for Unique Word Count, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_OverlapCollision
import Definitions.Def_DeletionCode_FinitePairUnion
import Definitions.Def_DeletionCode_UniqueWordParameters
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit true
namespace DeletionCode.UniqueWordCount
open Windows HeaderRecovery
attribute [local instance] Classical.propDecidable
noncomputable def uniqueWords (n k : ℕ) : Finset (Bits n) := by
  classical
  exact Finset.univ.filter (fun x => KUnique (padBits x) n k)
noncomputable def nonuniqueWords (n k : ℕ) : Finset (Bits n) := by
  classical
  exact Finset.univ.filter (fun x => ¬ KUnique (padBits x) n k)
def RepeatedWindow {n : ℕ} (k : ℕ) (a b : Fin n) (x : Bits n) : Prop :=
  a.val + k ≤ n ∧ b.val + k ≤ n ∧ Agree (padBits x) a.val (padBits x) b.val k
end DeletionCode.UniqueWordCount


