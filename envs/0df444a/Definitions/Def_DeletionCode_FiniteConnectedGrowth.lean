-- Prove2me | Definitions.Def_DeletionCode_FiniteConnectedGrowth
-- name    : DeletionCode_FiniteConnectedGrowth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:01:25.895216+00:00
-- url     : https://prove2.me/theorems/7d59f1f5-a21c-40ea-a000-ac918ea20a18
-- title:
--   Finite Connected Growth
-- statement:
--   Definitions and structural lemmas for Finite Connected Growth, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteConnectedGrowth.lean

import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Lean.Elab.Tactic.Omega
set_option autoImplicit true
namespace DeletionCode.FiniteConnectedGrowth
variable {α : Type*} [DecidableEq α]
def Induced (B : Finset α) (r : α → α → Prop) (u v : α) : Prop :=
  u ∈ B ∧ v ∈ B ∧ r u v
end DeletionCode.FiniteConnectedGrowth


