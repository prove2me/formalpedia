-- Prove2me | Definitions.Def_VerifiedHAMT_Bindings
-- name    : VerifiedHAMT_Bindings
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:25:33.224396+00:00
-- url     : https://prove2.me/theorems/be4c20c3-9452-44c3-a0db-e9cb46b0fb23
-- title:
--   Bindings
-- statement:
--   Definitions and structural lemmas for Bindings, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Bindings.lean

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
def Updated (before after : Node α β) (key : α) (value : β) : Prop :=
  ∀ q w, HasBinding q w after ↔
    (q = key ∧ w = value) ∨ (q ≠ key ∧ HasBinding q w before)
end VerifiedHAMT


