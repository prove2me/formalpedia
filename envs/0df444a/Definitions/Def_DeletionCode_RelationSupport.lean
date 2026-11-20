-- Prove2me | Definitions.Def_DeletionCode_RelationSupport
-- name    : DeletionCode_RelationSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:08:27.651124+00:00
-- url     : https://prove2.me/theorems/6a61afdc-279c-4487-b97b-0a78420373e9
-- title:
--   Relation Support
-- statement:
--   Definitions and structural lemmas for Relation Support, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationSupport.lean

import Definitions.Def_DeletionCode_WitnessAlgebra
set_option autoImplicit true
namespace DeletionCode.RelationSupport
open SignedSupport
open scoped BigOperators
def Relation {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ) : Prop :=
  ∀ g, (w g : ℚ) = ∑ i, a i * (G i g : ℚ)
end DeletionCode.RelationSupport


