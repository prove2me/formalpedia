-- Prove2me | Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
-- name    : VerifiedHAMT_SetWithoutValArray_Insert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:40:52.089092+00:00
-- url     : https://prove2.me/theorems/5302161f-cdb5-42be-86bc-bdb817eb4a47
-- title:
--   Insert
-- statement:
--   Definitions and structural lemmas for Insert, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Insert.lean

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
public import Theorems.Thm_VerifiedHAMT_DistinctKeys_push
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_DistinctKeys_push

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift branching maxDepth maxCollisions)
variable {α : Type u}
def insertCollisionAux [BEq α] (b : CollisionNode α) (i : Nat)
    (key : α) : CollisionNode α :=
  match b with
  | ⟨.collision keys, _⟩ =>
    if hi : i < keys.size then
      if key == keys[i] then
        ⟨.collision (keys.set i key), .mk ..⟩
      else insertCollisionAux b (i + 1) key
    else
      ⟨.collision (keys.push key), .mk ..⟩
  | ⟨.entries _, h⟩ => nomatch h
termination_by getCollisionNodeSize b - i
decreasing_by simp only [getCollisionNodeSize]; omega
@[inline] def insertCollision [BEq α] (keys : Array α)
    (key : α) : CollisionNode α :=
  insertCollisionAux ⟨.collision keys, .mk ..⟩ 0 key
@[inline] def insertEntries [BEq α]
    (es : Array (Entry α (Node α)))
    -- NOTE: `insertEntries` handles the current level; `childInsert` handles the next level.
    -- Only the `.ref` case consumes another hash chunk and invokes the callback.
    (childInsert : (child : Node α) → .ref child ∈ es → USize → α → Node α)
    (h : USize) (key : α) :
    Array (Entry α (Node α)) :=
  let i := slot h
  if hi : i < es.size then
    let old := es[i]
    -- NOTE: Clearing the slot before the recursive call leaves the child unshared
    -- whenever the array was, so the child can be updated in place. Every arm
    -- writes into the cleared array: in this shape the compiler keeps the
    -- clearing write before the recursion, which `VerifiedHAMTTests/ReleaseIR.lean` checks.
    let es' := es.set i .null
    have hi' : i < es'.size := by simpa [es'] using hi
    match he : old with
    | .null => es'.set i (.entry key) hi'
    | .entry k =>
      if key == k then es'.set i (.entry key) hi'
      else es'.set i (.ref (mkCollisionNode k key)) hi'
    | .ref child =>
      es'.set i (.ref (childInsert child (he ▸ Array.getElem_mem hi) (nextHash h) key)) hi'
  else es
def insertNoExpand [BEq α] (node : Node α) (hash : USize)
    (key : α) : Node α :=
  match node with
  | .collision keys =>
    (insertCollision keys key).val
  | .entries es =>
    .entries (insertEntries es (fun child _ => insertNoExpand child) hash key)
termination_by sizeOf node
decreasing_by
  have h := Array.sizeOf_lt_of_mem ‹_›
  simp at h ⊢
  omega
@[specialize] def rebuild [BEq α] [Hashable α]
    (childInsert : Node α → USize → α → Node α) (offset : USize)
    (b : CollisionNode α) (i : Nat) (es : Array (Entry α (Node α))) :
    Array (Entry α (Node α)) :=
  match b with
  | ⟨.collision keys, _⟩ =>
    if hi : i < keys.size then
      let key := keys[i]
      let h := (hash key).toUSize >>> offset
      rebuild childInsert offset b (i + 1) (insertEntries es (fun child _ => childInsert child) h key)
    else es
  | ⟨.entries _, h⟩ => nomatch h
termination_by getCollisionNodeSize b - i
decreasing_by simp only [getCollisionNodeSize]; omega
def insertNode [BEq α] [Hashable α] (levels : Nat) (offset : USize)
    (node : Node α) (h : USize) (key : α) : Node α :=
  match levels with
  | 0 => insertNoExpand node h key
  | levels + 1 =>
    match node with
    | .entries es => .entries (insertEntries es
        (fun child _ => insertNode levels (offset + shift) child) h key)
    | .collision keys =>
      let b := insertCollision keys key
      if getCollisionNodeSize b < maxCollisions then b.val
      -- NOTE: Rebuilding routes keys at the current `offset`, but its callback
      -- inserts into children with `offset + shift` and one fewer level. Calling
      -- full `insertNode` on the accumulator at the current level would not
      -- decrease `levels`; `insertEntries` performs that local step without recursion.
      else .entries (rebuild (insertNode levels (offset + shift))
        offset b 0 mkEmptyEntriesArray)
def insert [BEq α] [Hashable α] (map : Raw α)
    (key : α) : Raw α :=
  ⟨insertNode (maxDepth.toNat - 1) 0 map.root (hash key).toUSize key⟩
end VerifiedHAMT.SetWithoutValArray.Raw


