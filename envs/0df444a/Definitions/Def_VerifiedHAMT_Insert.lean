-- Prove2me | Definitions.Def_VerifiedHAMT_Insert
-- name    : VerifiedHAMT_Insert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:29:42.831992+00:00
-- url     : https://prove2.me/theorems/c8629642-5e31-4208-acc6-3c6b20fe305b
-- title:
--   Insert
-- statement:
--   Definitions and structural lemmas for Insert, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Insert.lean

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_Bindings
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Theorems.Thm_VerifiedHAMT_DistinctKeys_push

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
def insertCollisionAux [BEq α] (b : CollisionNode α β) (i : Nat)
    (key : α) (value : β) : CollisionNode α β :=
  match b with
  | ⟨.collision keys vals hsz, _⟩ =>
    -- FIXME: Ideally, should not compare with `key.size` repetitively?
    if hi : i < keys.size then
      if key == keys[i] then
        ⟨.collision (keys.set i key) (vals.set i value (hsz ▸ hi))
          (by simp [hsz]), .mk ..⟩
      else insertCollisionAux b (i + 1) key value
    else
      ⟨.collision (keys.push key) (vals.push value) (by simp [hsz]), .mk ..⟩
  | ⟨.entries _, h⟩ => nomatch h
termination_by getCollisionNodeSize b - i
decreasing_by simp only [getCollisionNodeSize]; omega
@[inline] def insertCollision [BEq α] (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (key : α) (value : β) : CollisionNode α β :=
  insertCollisionAux ⟨.collision keys vals hsz, .mk ..⟩ 0 key value
@[inline] def insertEntries [BEq α]
    (es : Array (Entry α β (Node α β)))
    -- NOTE: `insertEntries` handles the current level; `childInsert` handles the next level.
    -- Only the `.ref` case consumes another hash chunk and invokes the callback.
    (childInsert : (child : Node α β) → .ref child ∈ es → USize → α → β → Node α β)
    (h : USize) (key : α) (value : β) :
    Array (Entry α β (Node α β)) :=
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
    | .null => es'.set i (.entry key value) hi'
    | .entry k v =>
      if key == k then es'.set i (.entry key value) hi'
      else es'.set i (.ref (mkCollisionNode k v key value)) hi'
    | .ref child =>
      es'.set i (.ref (childInsert child (he ▸ Array.getElem_mem hi) (nextHash h) key value)) hi'
  else es
def insertNoExpand [BEq α] (node : Node α β) (hash : USize)
    (key : α) (value : β) : Node α β :=
  match node with
  | .collision keys vals hsz =>
    (insertCollision keys vals hsz key value).val
  | .entries es =>
    .entries (insertEntries es (fun child _ => insertNoExpand child) hash key value)
termination_by sizeOf node
decreasing_by
  have h := Array.sizeOf_lt_of_mem ‹_›
  simp at h ⊢
  omega
@[specialize] def rebuild [BEq α] [Hashable α]
    (childInsert : Node α β → USize → α → β → Node α β) (offset : USize)
    (b : CollisionNode α β) (i : Nat) (es : Array (Entry α β (Node α β))) :
    Array (Entry α β (Node α β)) :=
  match b with
  | ⟨.collision keys vals hsz, _⟩ =>
    -- FIXME: Ideally, should not compare with `key.size` repetitively?
    if hi : i < keys.size then
      let key := keys[i]
      let h := (hash key).toUSize >>> offset
      let val := vals[i]'(hsz ▸ hi)
      rebuild childInsert offset b (i + 1) (insertEntries es (fun child _ => childInsert child) h key val)
    else es
  | ⟨.entries _, h⟩ => nomatch h
termination_by getCollisionNodeSize b - i
decreasing_by simp only [getCollisionNodeSize]; omega
def insertNode [BEq α] [Hashable α] (levels : Nat) (offset : USize)
    (node : Node α β) (h : USize) (key : α) (value : β) : Node α β :=
  match levels with
  | 0 => insertNoExpand node h key value
  | levels + 1 =>
    match node with
    | .entries es => .entries (insertEntries es
        (fun child _ => insertNode levels (offset + shift) child) h key value)
    | .collision keys vals hsz =>
      let b := insertCollision keys vals hsz key value
      if getCollisionNodeSize b < maxCollisions then b.val
      -- NOTE: Rebuilding routes keys at the current `offset`, but its callback
      -- inserts into children with `offset + shift` and one fewer level. Calling
      -- full `insertNode` on the accumulator at the current level would not
      -- decrease `levels`; `insertEntries` performs that local step without recursion.
      else .entries (rebuild (insertNode levels (offset + shift))
        offset b 0 mkEmptyEntriesArray)
def insert [BEq α] [Hashable α] (map : Lean.PersistentHashMap α β)
    (key : α) (value : β) : Lean.PersistentHashMap α β :=
  ⟨insertNode (maxDepth.toNat - 1) 0 map.root (hash key).toUSize key value⟩
end VerifiedHAMT


