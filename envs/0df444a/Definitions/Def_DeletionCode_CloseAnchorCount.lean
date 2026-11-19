-- Prove2me | Definitions.Def_DeletionCode_CloseAnchorCount
-- name    : DeletionCode_CloseAnchorCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:04:32.734672+00:00
-- url     : https://prove2.me/theorems/b2961313-58ef-4ce2-9f65-f27169f28675
-- title:
--   Close Anchor Count
-- statement:
--   Definitions and structural lemmas for Close Anchor Count, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CloseAnchorCount.lean

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option autoImplicit true
namespace DeletionCode.CloseAnchorCount
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
def Bad {r n : ℕ} (m B : ℕ) (a : Fin r → Fin n) : Prop :=
  (∃ i, (a i).val < B) ∨
  (∃ i, Nat.dist (a i).val m < B) ∨
  (∃ i j, i ≠ j ∧ Nat.dist (a i).val (a j).val < B)
abbrev EventIndex (r : ℕ) := Fin r × (Fin r ⊕ Bool)
def Event {r n : ℕ} (m B : ℕ) (q : EventIndex r) (a : Fin r → Fin n) : Prop :=
  match q.2 with
  | .inl j => q.1 ≠ j ∧ Nat.dist (a q.1).val (a j).val < B
  | .inr false => (a q.1).val < B
  | .inr true => Nat.dist (a q.1).val m < B
end
end DeletionCode.CloseAnchorCount


