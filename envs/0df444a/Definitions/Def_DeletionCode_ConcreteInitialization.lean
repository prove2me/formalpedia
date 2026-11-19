-- Prove2me | Definitions.Def_DeletionCode_ConcreteInitialization
-- name    : DeletionCode_ConcreteInitialization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:08:45.41213+00:00
-- url     : https://prove2.me/theorems/3ec42bc8-81fd-404f-b8ff-ba63e5a195b1
-- title:
--   Concrete Initialization
-- statement:
--   Definitions and structural lemmas for Concrete Initialization, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteInitialization.lean

import Definitions.Def_DeletionCode_ConcreteModel
set_option autoImplicit true
namespace DeletionCode.ConcreteInitialization
open Windows HeaderRecovery PartialWords SelectedWindows ConcreteDecoder ConcreteModel
variable {B : Type*} {x : Letters} {n k : ℕ}
def ValidRoots (M : Model B x n k) (records : List (B × ℕ)) : Prop :=
  ∀ b a, (b, a) ∈ records → a + negativeLength k (M.header b) ≤ n ∧
    Agree x a (negativePath k (M.header b) (M.long b)) 0 (negativeLength k (M.header b))
noncomputable def rootCount [Fintype B] (M : Model B x n k) : ℕ := by
  classical
  exact (Finset.univ.filter M.schedule.root).card
end DeletionCode.ConcreteInitialization


