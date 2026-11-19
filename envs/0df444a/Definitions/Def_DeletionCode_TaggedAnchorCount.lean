-- Prove2me | Definitions.Def_DeletionCode_TaggedAnchorCount
-- name    : DeletionCode_TaggedAnchorCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:07:04.506735+00:00
-- url     : https://prove2.me/theorems/b159782e-0084-4c85-bbe0-2bfe8b77abc9
-- title:
--   Tagged Anchor Count
-- statement:
--   Definitions and structural lemmas for Tagged Anchor Count, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TaggedAnchorCount.lean

import Definitions.Def_DeletionCode_CloseAnchorCount
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum
set_option autoImplicit true
namespace DeletionCode.TaggedAnchorCount
abbrev Record (n r : ℕ) := (Fin r → Fin n) × (Fin r → Bool × Bool)
def packets {n r : ℕ} (rec : Record n r) : List (ℕ × (Bool × Bool)) :=
  List.ofFn (fun i => ((rec.1 i).val, rec.2 i))
def Bad {n r : ℕ} (m B : ℕ) (rec : Record n r) : Prop :=
  CloseAnchorCount.Bad m B rec.1
noncomputable def badEquiv (n r m B : ℕ) :
    {rec : Record n r // Bad m B rec} ≃
      {a : Fin r → Fin n // CloseAnchorCount.Bad m B a} × (Fin r → Bool × Bool) where
  toFun rec := (⟨rec.val.1, rec.property⟩, rec.val.2)
  invFun p := ⟨(p.1.val, p.2), p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
end DeletionCode.TaggedAnchorCount


