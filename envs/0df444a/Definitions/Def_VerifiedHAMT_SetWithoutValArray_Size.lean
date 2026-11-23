-- Prove2me | Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
-- name    : VerifiedHAMT_SetWithoutValArray_Size
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:31:25.141905+00:00
-- url     : https://prove2.me/theorems/bb05a19b-bf0b-4709-a081-5d11ed19e048
-- title:
--   Size
-- statement:
--   Definitions and structural lemmas for Size, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
mutual
/-- The keys stored in a node, in slot order. A key stored twice, which the invariants
exclude, is listed twice. -/
def keyList : Node α → List α
  | .entries es => entriesKeyList es
  | .collision keys => keys.toList

/-- The keys stored in an entries array. -/
def entriesKeyList : Array (Entry α (Node α)) → List α
  | ⟨es⟩ => entryListKeyList es

/-- The keys stored in a list of entries. -/
def entryListKeyList : List (Entry α (Node α)) → List α
  | [] => []
  | e :: es => entryKeyList e ++ entryListKeyList es

/-- The keys stored in an entry. -/
def entryKeyList : Entry α (Node α) → List α
  | .null => []
  | .entry key => [key]
  | .ref child => keyList child
end
def keyCount (node : Node α) : Nat := (keyList node).length
end VerifiedHAMT.SetWithoutValArray.Raw


