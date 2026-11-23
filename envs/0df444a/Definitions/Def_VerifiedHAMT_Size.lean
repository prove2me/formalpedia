-- Prove2me | Definitions.Def_VerifiedHAMT_Size
-- name    : VerifiedHAMT_Size
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:25:13.04716+00:00
-- url     : https://prove2.me/theorems/a72bfa6b-43b4-4878-a389-66887b12565d
-- title:
--   Size
-- statement:
--   Definitions and structural lemmas for Size, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Size.lean

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
mutual
/-- The keys stored in a node, in slot order. A key stored twice, which the invariants
exclude, is listed twice. -/
def keyList : Node α β → List α
  | .entries es => entriesKeyList es
  | .collision keys _ _ => keys.toList

/-- The keys stored in an entries array. -/
def entriesKeyList : Array (Entry α β (Node α β)) → List α
  | ⟨es⟩ => entryListKeyList es

/-- The keys stored in a list of entries. -/
def entryListKeyList : List (Entry α β (Node α β)) → List α
  | [] => []
  | e :: es => entryKeyList e ++ entryListKeyList es

/-- The keys stored in an entry. -/
def entryKeyList : Entry α β (Node α β) → List α
  | .null => []
  | .entry key _ => [key]
  | .ref child => keyList child
end
def keyCount (node : Node α β) : Nat := (keyList node).length
end VerifiedHAMT


