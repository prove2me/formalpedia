-- Prove2me | Definitions.Def_DeletionCode_SingleEditOrigins
-- name    : DeletionCode_SingleEditOrigins
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:11:47.003829+00:00
-- url     : https://prove2.me/theorems/5dbb15ff-a77a-4469-9e5b-6ecb61ca212b
-- title:
--   Single Edit Origins
-- statement:
--   Definitions and structural lemmas for Single Edit Origins, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditOrigins.lean

import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
namespace DeletionCode.SingleEditOrigins
open Windows
inductive Edit where
  | unchanged
  | delete (pos : ℕ)
  | insert (pos : ℕ) (bit : Bool)
  deriving DecidableEq, Repr
namespace Edit
def cut : Edit → ℕ
  | .unchanged => 0
  | .delete pos => pos
  | .insert pos _ => pos
def outputLength (e : Edit) (n : ℕ) : ℕ :=
  match e with
  | .unchanged => n
  | .delete _ => n - 1
  | .insert _ _ => n + 1
def Valid (e : Edit) (n : ℕ) : Prop :=
  match e with
  | .unchanged => True
  | .delete pos => pos < n
  | .insert pos _ => pos ≤ n
def word (e : Edit) (x : Letters) : Letters :=
  match e with
  | .unchanged => x
  | .delete pos => deleteAt x pos
  | .insert pos bit => insertAt x pos bit
def origin (e : Edit) (i : ℕ) : Option ℕ :=
  match e with
  | .unchanged => some i
  | .delete pos => some (if i < pos then i else i + 1)
  | .insert pos _ =>
      if i < pos then some i else if i = pos then none else some (i - 1)
end Edit
end DeletionCode.SingleEditOrigins


