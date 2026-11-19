-- Prove2me | Definitions.Def_DeletionCode_RecordPacking
-- name    : DeletionCode_RecordPacking
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:00:51.905201+00:00
-- url     : https://prove2.me/theorems/6b061dae-36ae-44c4-9d3b-d5bd3d37f709
-- title:
--   Record Packing
-- statement:
--   Definitions and structural lemmas for Record Packing, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordPacking.lean

import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega
set_option autoImplicit true
namespace DeletionCode.RecordPacking
variable {α β : Type*}
def pack (padding : β) (xs : List β) (size : ℕ) : Fin size → β :=
  fun i => xs[i.val]?.getD padding
def unpack (decode : β → Option (Option α)) :
    (size : ℕ) → (Fin size → β) → Option (List α)
  | 0, _ => some []
  | size + 1, rows =>
    (decode (rows ⟨0, by omega⟩)).bind fun entry =>
      (unpack decode size (fun i => rows i.succ)).map fun rest => entry.toList ++ rest
end DeletionCode.RecordPacking


