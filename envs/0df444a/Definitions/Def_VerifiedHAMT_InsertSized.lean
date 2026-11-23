-- Prove2me | Definitions.Def_VerifiedHAMT_InsertSized
-- name    : VerifiedHAMT_InsertSized
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:31:51.372227+00:00
-- url     : https://prove2.me/theorems/6c4a7c31-62ad-40de-8550-9525f1ffc45b
-- title:
--   Insert Sized
-- statement:
--   Definitions and structural lemmas for Insert Sized, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertSized.lean

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
structure SizedRaw (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  /-- The native map, or the child currently being updated during insertion. -/
  toRaw : Lean.PersistentHashMap α β
  /-- The total map size. `Map` additionally proves that this counts its keys. -/
  size : Nat
@[inline] def insertSizedEntries [BEq α] [Hashable α]
    (es : Array (Entry α β (Node α β))) (size : Nat)
    (childInsert : (child : Node α β) → .ref child ∈ es →
      Nat → USize → α → β → SizedRaw α β)
    (h : USize) (key : α) (value : β) : SizedRaw α β :=
  let i := slot h
  if hi : i < es.size then
    let old := es[i]
    -- NOTE: As in `insertEntries`, clear the slot before the recursive call and
    -- write every arm into the cleared array, so that an unshared child is updated
    -- in place. The size travels back with the child's result.
    let es' := es.set i .null
    have hi' : i < es'.size := by simpa [es'] using hi
    match he : old with
    | .null => ⟨⟨.entries (es'.set i (.entry key value) hi')⟩, size + 1⟩
    | .entry k v =>
      if key == k then ⟨⟨.entries (es'.set i (.entry key value) hi')⟩, size⟩
      else ⟨⟨.entries (es'.set i (.ref (mkCollisionNode k v key value)) hi')⟩, size + 1⟩
    | .ref child =>
      let result := childInsert child (he ▸ Array.getElem_mem hi) size (nextHash h) key value
      ⟨⟨.entries (es'.set i (.ref result.toRaw.root) hi')⟩, result.size⟩
  -- The reference lookup returns false for an invalid slot; preserve its
  -- size specification even though the entries array is left unchanged.
  else ⟨⟨.entries es⟩, size + 1⟩
def insertSizedNoExpand [BEq α] [Hashable α] (s : SizedRaw α β) (h : USize)
    (key : α) (value : β) : SizedRaw α β :=
  let ⟨⟨node⟩, size⟩ := s
  match node with
  | .collision keys vals hsz =>
    let oldSize := keys.size
    let b := insertCollisionAux ⟨.collision keys vals hsz, .mk ..⟩ 0 key value
    let size := if getCollisionNodeSize b == oldSize then size else size + 1
    ⟨⟨b.val⟩, size⟩
  | .entries es =>
    insertSizedEntries es size (fun child _ size =>
      insertSizedNoExpand ⟨⟨child⟩, size⟩) h key value
termination_by sizeOf s.toRaw.root
decreasing_by
  have hs := Array.sizeOf_lt_of_mem ‹_›
  simp at hs ⊢
  omega
def insertSizedRaw [BEq α] [Hashable α] (levels : Nat) (offset : USize)
    (s : SizedRaw α β) (h : USize) (key : α) (value : β) : SizedRaw α β :=
  match levels with
  | 0 => insertSizedNoExpand s h key value
  | levels + 1 =>
    let ⟨⟨node⟩, size⟩ := s
    match node with
    | .entries es =>
      insertSizedEntries es size (fun child _ size =>
        insertSizedRaw levels (offset + shift) ⟨⟨child⟩, size⟩) h key value
    | .collision keys vals hsz =>
      let oldSize := keys.size
      let b := insertCollision keys vals hsz key value
      let size := if getCollisionNodeSize b == oldSize then size else size + 1
      if getCollisionNodeSize b < maxCollisions then ⟨⟨b.val⟩, size⟩
      else ⟨⟨.entries (rebuild (insertNode levels (offset + shift))
        offset b 0 mkEmptyEntriesArray)⟩, size⟩
@[inline] def insertSizedImpl [BEq α] [Hashable α] (s : SizedRaw α β)
    (key : α) (value : β) : SizedRaw α β :=
  insertSizedRaw (maxDepth.toNat - 1) 0 s (hash key).toUSize key value
def insertSized [BEq α] [Hashable α] (s : SizedRaw α β)
    (key : α) (value : β) : SizedRaw α β :=
  ⟨insert s.toRaw key value,
    if containsNode s.toRaw.root (hash key).toUSize key then s.size else s.size + 1⟩
end VerifiedHAMT


