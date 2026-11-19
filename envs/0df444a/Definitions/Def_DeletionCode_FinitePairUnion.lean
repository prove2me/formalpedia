-- Prove2me | Definitions.Def_DeletionCode_FinitePairUnion
-- name    : DeletionCode_FinitePairUnion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:03:08.7078+00:00
-- url     : https://prove2.me/theorems/5737e9f3-7935-4ce2-8692-23b3cd9ee5b0
-- title:
--   Finite Pair Union
-- statement:
--   Definitions and structural lemmas for Finite Pair Union, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FinitePairUnion.lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
set_option autoImplicit true
namespace DeletionCode.FinitePairUnion
open scoped BigOperators
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
abbrev OrderedPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
def orderedPairEquiv (n : ℕ) : OrderedPair n ≃ Σ b : Fin n, Fin b.val where
  toFun p := ⟨p.val.2, ⟨p.val.1.val, p.property⟩⟩
  invFun p := ⟨(⟨p.2.val, p.2.isLt.trans p.1.isLt⟩, p.1), p.2.isLt⟩
  left_inv := by rintro ⟨⟨a, b⟩, hab⟩; rfl
  right_inv := by rintro ⟨b, a⟩; rfl
end
end DeletionCode.FinitePairUnion


