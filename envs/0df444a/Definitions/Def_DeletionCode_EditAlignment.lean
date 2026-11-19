-- Prove2me | Definitions.Def_DeletionCode_EditAlignment
-- name    : DeletionCode_EditAlignment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:01:21.086054+00:00
-- url     : https://prove2.me/theorems/1da3e1e0-f0ce-4ec0-9e8c-0a0e53fd9afb
-- title:
--   Edit Alignment
-- statement:
--   Definitions and structural lemmas for Edit Alignment, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditAlignment.lean

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
set_option autoImplicit true
namespace DeletionCode.EditAlignment
abbrev Word := List Bool
inductive Script : Word → Word → ℕ → ℕ → Prop
  | refl (word : Word) : Script word word 0 0
  | delete {y pre suffix : Word} {bit : Bool} {d i : ℕ} :
      Script y (pre ++ bit :: suffix) d i → Script y (pre ++ suffix) (d + 1) i
  | insert {y pre suffix : Word} {bit : Bool} {d i : ℕ} :
      Script y (pre ++ suffix) d i → Script y (pre ++ bit :: suffix) d (i + 1)
inductive Alignment : Word → Word → ℕ → ℕ → Prop
  | nil : Alignment [] [] 0 0
  | matched (bit : Bool) {y z : Word} {d i : ℕ} :
      Alignment y z d i → Alignment (bit :: y) (bit :: z) d i
  | deletion (bit : Bool) {y z : Word} {d i : ℕ} :
      Alignment y z d i → Alignment (bit :: y) z (d + 1) i
  | insertion (bit : Bool) {y z : Word} {d i : ℕ} :
      Alignment y z d i → Alignment y (bit :: z) d (i + 1)
def WithinEdits (t : ℕ) (y z : Word) : Prop :=
  ∃ d i, Script y z d i ∧ d + i ≤ t
end DeletionCode.EditAlignment


