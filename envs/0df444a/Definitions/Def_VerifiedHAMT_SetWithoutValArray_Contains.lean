-- Prove2me | Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
-- name    : VerifiedHAMT_SetWithoutValArray_Contains
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:31:23.838974+00:00
-- url     : https://prove2.me/theorems/cc382249-b98b-436c-ae4f-0c4794fa185c
-- title:
--   Contains
-- statement:
--   Definitions and structural lemmas for Contains, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Contains.lean

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
def containsNode [BEq α] (node : Node α) (hash : USize) (key : α) : Bool :=
  match node with
  -- NOTE: `contains` uses `Array.any`, which in turn uses `Array.anyM`,
  -- which seems optimized?
  | .collision keys => keys.contains key
  | .entries es =>
    let i := slot hash
    if hi : i < es.size then
      match he : es[i] with
      | .null => false
      | .entry key' => key == key'
      | .ref child => containsNode child (nextHash hash) key
    else false
termination_by sizeOf node
decreasing_by
  have h := Array.sizeOf_get es i hi
  rw [he] at h
  simp at h ⊢
  omega
def contains [BEq α] [Hashable α] (map : Raw α) (key : α) : Bool :=
  containsNode map.root (hash key).toUSize key
end VerifiedHAMT.SetWithoutValArray.Raw


