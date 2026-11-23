-- Prove2me | Definitions.Def_VerifiedHAMT_Contains
-- name    : VerifiedHAMT_Contains
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:25:13.387476+00:00
-- url     : https://prove2.me/theorems/8cf65f11-46cf-4e5d-86c5-d84a14129c42
-- title:
--   Contains
-- statement:
--   Definitions and structural lemmas for Contains, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Contains.lean

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
def containsNode [BEq α] (node : Node α β) (hash : USize) (key : α) : Bool :=
  match node with
  -- NOTE: `contains` uses `Array.any`, which in turn uses `Array.anyM`,
  -- which seems optimized?
  | .collision keys _ _ => keys.contains key
  | .entries es =>
    let i := slot hash
    if hi : i < es.size then
      match he : es[i] with
      | .null => false
      | .entry key' _ => key == key'
      | .ref child => containsNode child (nextHash hash) key
    else false
termination_by sizeOf node
decreasing_by
  have h := Array.sizeOf_get es i hi
  rw [he] at h
  simp at h ⊢
  omega
def contains [BEq α] [Hashable α] (map : Lean.PersistentHashMap α β) (key : α) : Bool :=
  containsNode map.root (hash key).toUSize key
end VerifiedHAMT


