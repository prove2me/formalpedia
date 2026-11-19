-- Prove2me | Definitions.Def_DeletionCode_AlignmentTrace
-- name    : DeletionCode_AlignmentTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:02:29.062203+00:00
-- url     : https://prove2.me/theorems/6c29d04f-0859-4b9d-bd93-c46a40914cf0
-- title:
--   Alignment Trace
-- statement:
--   Definitions and structural lemmas for Alignment Trace, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AlignmentTrace.lean

import Definitions.Def_DeletionCode_EditAlignment
set_option autoImplicit true
namespace DeletionCode.AlignmentTrace
open EditAlignment
inductive Column where
  | matched (bit : Bool)
  | deletion (bit : Bool)
  | insertion (bit : Bool)
  deriving DecidableEq, Repr
def Column.isEdit : Column → Bool
  | .matched _ => false
  | .deletion _ => true
  | .insertion _ => true
abbrev Trace := List Column
namespace Trace
def source : Trace → Word
  | [] => []
  | .matched bit :: rest => bit :: source rest
  | .deletion bit :: rest => bit :: source rest
  | .insertion _ :: rest => source rest
def target : Trace → Word
  | [] => []
  | .matched bit :: rest => bit :: target rest
  | .deletion _ :: rest => target rest
  | .insertion bit :: rest => bit :: target rest
def deletions : Trace → ℕ
  | [] => 0
  | .matched _ :: rest => deletions rest
  | .deletion _ :: rest => deletions rest + 1
  | .insertion _ :: rest => deletions rest
def insertions : Trace → ℕ
  | [] => 0
  | .matched _ :: rest => insertions rest
  | .deletion _ :: rest => insertions rest
  | .insertion _ :: rest => insertions rest + 1
def matchedCount : Trace → ℕ
  | [] => 0
  | .matched _ :: rest => matchedCount rest + 1
  | .deletion _ :: rest => matchedCount rest
  | .insertion _ :: rest => matchedCount rest
def matchedAnchor (trace : Trace) (j : ℕ) : ℕ := matchedCount (trace.take j)
def sourcePosition (trace : Trace) (j : ℕ) : ℕ := (source (trace.take j)).length
def targetPosition (trace : Trace) (j : ℕ) : ℕ := (target (trace.take j)).length
end Trace
end DeletionCode.AlignmentTrace


