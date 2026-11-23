-- Prove2me | Definitions.Def_VerifiedHAMT_Find
-- name    : VerifiedHAMT_Find
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:32:28.60583+00:00
-- url     : https://prove2.me/theorems/bf53da39-b298-4202-9c89-71b1760b3402
-- title:
--   Find
-- statement:
--   Definitions and structural lemmas for Find, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
def findCollisionAux [BEq α] (keys : Array α) (vals : Array β)
    (hsz : keys.size = vals.size) (i : Nat) (key : α) : Option β :=
  if hi : i < keys.size then
    if key == keys[i] then some (vals[i]'(hsz ▸ hi))
    else findCollisionAux keys vals hsz (i + 1) key
  else none
termination_by keys.size - i
def findNode [BEq α] (node : @& Node α β) (hash : USize) (key : α) : Option β :=
  match node with
  | .collision keys vals hsz => findCollisionAux keys vals hsz 0 key
  | .entries es =>
    if hi : slot hash < es.size then
      match he : es[slot hash] with
      | .null => none
      | .entry key' value => if key == key' then some value else none
      | .ref child => findNode child (nextHash hash) key
    else none
termination_by sizeOf node
decreasing_by
  have h := Array.sizeOf_get es (slot hash) hi
  rw [he] at h
  simp at h ⊢
  omega
def find? [BEq α] [Hashable α] (map : @& Lean.PersistentHashMap α β) (key : α) : Option β :=
  findNode map.root (hash key).toUSize key
@[inline] def findD [BEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (key : α) (fallback : β) : β :=
  (find? map key).getD fallback
section Soundness
end Soundness
section Completeness
end Completeness
section MainParts
end MainParts
section DerivedParts
end DerivedParts
end VerifiedHAMT


