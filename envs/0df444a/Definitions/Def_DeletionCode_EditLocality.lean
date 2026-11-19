-- Prove2me | Definitions.Def_DeletionCode_EditLocality
-- name    : DeletionCode_EditLocality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:32:09.983202+00:00
-- url     : https://prove2.me/theorems/268ced50-2f94-4d84-86bd-1997db336e52
-- title:
--   Edit Locality
-- statement:
--   Definitions and structural lemmas for Edit Locality, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditLocality.lean

import Definitions.Def_DeletionCode_EditRigidity
import Mathlib.Order.Interval.Set.Basic
set_option autoImplicit true
namespace DeletionCode.EditLocality
open Windows HeaderRecovery SingleEditOrigins
def Inside (e : Edit) (start len : ℕ) : Prop :=
  match e with
  | .unchanged => True
  | .delete pos => start ≤ pos ∧ pos < start + len
  | .insert pos _ => start ≤ pos ∧ pos ≤ start + len
def localVertices (e : Edit) (x : Letters) (start len L : ℕ) :
    Set (SupportComponents.Vertex L) :=
  {v | ∃ a, start ≤ a ∧ a + (L - 1) ≤ start + e.outputLength len ∧
    SpectrumPath.vertexAt (e.word x) L a = v}
end DeletionCode.EditLocality


