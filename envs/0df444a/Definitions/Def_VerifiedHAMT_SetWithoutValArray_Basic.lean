-- Prove2me | Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
-- name    : VerifiedHAMT_SetWithoutValArray_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:29:39.035084+00:00
-- url     : https://prove2.me/theorems/8666c2d9-b719-4e7a-9789-cde324c2a1e8
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Theorems.Thm_VerifiedHAMT_DistinctKeys_push

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace VerifiedHAMT.SetWithoutValArray
open Lean.PersistentHashMap (branching maxCollisions)
inductive Entry (α : Type u) (σ : Type v) where
  | entry (key : α)
  | ref (node : σ)
  | null
instance : Inhabited (Entry α σ) := ⟨.null⟩
inductive Node (α : Type u) where
  | entries (es : Array (Entry α (Node α)))
  | collision (keys : Array α)
instance : Inhabited (Node α) := ⟨.entries #[]⟩
def mkEmptyEntriesArray : Array (Entry α (Node α)) :=
  Array.replicate branching.toNat .null
def mkEmptyEntries : Node α := .entries mkEmptyEntriesArray
inductive IsCollisionNode : Node α → Prop where
  | mk (keys : Array α) : IsCollisionNode (.collision keys)
abbrev CollisionNode (α : Type u) := { n : Node α // IsCollisionNode n }
@[noinline] def getCollisionNodeSize : CollisionNode α → Nat
  | ⟨.collision keys, _⟩ => keys.size
  | ⟨.entries _, h⟩ => nomatch h
def mkCollisionNode (k₁ k₂ : α) : Node α :=
  .collision ((Array.mkEmpty maxCollisions).push k₁ |>.push k₂)
end VerifiedHAMT.SetWithoutValArray
structure VerifiedHAMT.SetWithoutValArray.Raw (α : Type u) [BEq α] [Hashable α] where
  root : SetWithoutValArray.Node α := SetWithoutValArray.mkEmptyEntries
namespace VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)
@[inline] def empty [BEq α] [Hashable α] : Raw α := {}
instance [BEq α] [Hashable α] : EmptyCollection (Raw α) := ⟨empty⟩
instance [BEq α] [Hashable α] : Inhabited (Raw α) := ⟨empty⟩
section HasKey
inductive HasKey (key : α) : Node α → Prop where
  | entry {es : Array (Entry α (Node α))} {i : Nat} {hi : i < es.size}
      (atIndex : es[i] = .entry key) : HasKey key (.entries es)
  | ref {es : Array (Entry α (Node α))} {i : Nat} {hi : i < es.size}
      {child : Node α} (atIndex : es[i] = .ref child)
      (inChild : HasKey key child) : HasKey key (.entries es)
  | collision {keys : Array α}
      (inKeys : key ∈ keys) : HasKey key (.collision keys)
def Mem [BEq α] [Hashable α] (key : α) (map : VerifiedHAMT.SetWithoutValArray.Raw α) : Prop :=
  HasKey key map.root
def EntryHasKey (key : α) : Entry α (Node α) → Prop
  | .null => False
  | .entry key' => key = key'
  | .ref child => HasKey key child
end HasKey
section WellFormed
inductive WellFormed : (α → USize) → Node α → Prop where
  | collision (hashAt : α → USize) (keys : Array α) : WellFormed hashAt (.collision keys)
  | entries {hashAt : α → USize} {es : Array (Entry α (Node α))}
      (size_eq : es.size = branching.toNat)
      (routing : ∀ (i : Nat) (hi : i < es.size) (key : α),
        EntryHasKey key es[i] → slot (hashAt key) = i)
      (children : ∀ (i : Nat) (hi : i < es.size) (child : Node α),
        es[i] = .ref child → WellFormed (fun key => nextHash (hashAt key)) child) :
      WellFormed hashAt (.entries es)
def Valid [BEq α] [Hashable α] (map : VerifiedHAMT.SetWithoutValArray.Raw α) : Prop :=
  WellFormed (fun key => (hash key).toUSize) map.root
end WellFormed
section Uniqueness
def DistinctKeys (keys : Array α) : Prop :=
  ∀ (i : Nat) (hi : i < keys.size) (j : Nat) (hj : j < keys.size),
    keys[i] = keys[j] → i = j
inductive Unique : Node α → Prop where
  | collision {keys : Array α}
      (distinct : DistinctKeys keys) : Unique (.collision keys)
  | entries {es : Array (Entry α (Node α))}
      (children : ∀ (i : Nat) (hi : i < es.size) (child : Node α),
        es[i] = .ref child → Unique child) : Unique (.entries es)
end Uniqueness
end VerifiedHAMT.SetWithoutValArray.Raw


