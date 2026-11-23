-- Prove2me | Definitions.Def_VerifiedHAMT_Basic
-- name    : VerifiedHAMT_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:24:56.761682+00:00
-- url     : https://prove2.me/theorems/6906dbd2-3f5b-4861-a52e-8c769b0944b5
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
section HasKey
inductive HasKey (key : α) : Node α β → Prop where
  | entry {es : Array (Entry α β (Node α β))} {i : Nat} {hi : i < es.size} {v : β}
      (atIndex : es[i] = .entry key v) : HasKey key (.entries es)
  | ref {es : Array (Entry α β (Node α β))} {i : Nat} {hi : i < es.size}
      {child : Node α β} (atIndex : es[i] = .ref child)
      (inChild : HasKey key child) : HasKey key (.entries es)
  | collision {keys : Array α} {vals : Array β} {hsz : keys.size = vals.size}
      (inKeys : key ∈ keys) : HasKey key (.collision keys vals hsz)
def Mem [BEq α] [Hashable α] (key : α) (map : Lean.PersistentHashMap α β) : Prop :=
  HasKey key map.root
def EntryHasKey (key : α) : Entry α β (Node α β) → Prop
  | .null => False
  | .entry key' _ => key = key'
  | .ref child => HasKey key child
end HasKey
@[inline] def slot (hash : USize) : Nat := (mod2Shift hash shift).toNat
@[inline] def nextHash (hash : USize) : USize := div2Shift hash shift
section WellFormed
inductive WellFormed : (α → USize) → Node α β → Prop where
  | collision (hashAt : α → USize) (keys : Array α) (vals : Array β)
      (hsz : keys.size = vals.size) : WellFormed hashAt (.collision keys vals hsz)
  | entries {hashAt : α → USize} {es : Array (Entry α β (Node α β))}
      (size_eq : es.size = branching.toNat)
      (routing : ∀ (i : Nat) (hi : i < es.size) (key : α),
        EntryHasKey key es[i] → slot (hashAt key) = i)
      (children : ∀ (i : Nat) (hi : i < es.size) (child : Node α β),
        es[i] = .ref child → WellFormed (fun key => nextHash (hashAt key)) child) :
      WellFormed hashAt (.entries es)
def Valid [BEq α] [Hashable α] (map : Lean.PersistentHashMap α β) : Prop :=
  WellFormed (fun key => (hash key).toUSize) map.root
end WellFormed
section HasBinding
inductive HasBinding (key : α) (value : β) : Node α β → Prop where
  | entry {es : Array (Entry α β (Node α β))} {i : Nat} {hi : i < es.size}
      (atIndex : es[i] = .entry key value) : HasBinding key value (.entries es)
  | ref {es : Array (Entry α β (Node α β))} {i : Nat} {hi : i < es.size}
      {child : Node α β} (atIndex : es[i] = .ref child)
      (inChild : HasBinding key value child) : HasBinding key value (.entries es)
  | collision {keys : Array α} {vals : Array β} {hsz : keys.size = vals.size}
      {i : Nat} (hi : i < keys.size) (hk : keys[i] = key)
      (hv : vals[i]'(hsz ▸ hi) = value) : HasBinding key value (.collision keys vals hsz)
def EntryHasBinding (key : α) (value : β) : Entry α β (Node α β) → Prop
  | .null => False
  | .entry k v => key = k ∧ value = v
  | .ref child => HasBinding key value child
end HasBinding
def MapsTo [BEq α] [Hashable α] (key : α) (value : β)
    (map : Lean.PersistentHashMap α β) : Prop := HasBinding key value map.root
section Uniqueness
def DistinctKeys (keys : Array α) : Prop :=
  ∀ (i : Nat) (hi : i < keys.size) (j : Nat) (hj : j < keys.size),
    keys[i] = keys[j] → i = j
inductive Unique : Node α β → Prop where
  | collision {keys : Array α} {vals : Array β} {hsz : keys.size = vals.size}
      (distinct : DistinctKeys keys) : Unique (.collision keys vals hsz)
  | entries {es : Array (Entry α β (Node α β))}
      (children : ∀ (i : Nat) (hi : i < es.size) (child : Node α β),
        es[i] = .ref child → Unique child) : Unique (.entries es)
end Uniqueness
end VerifiedHAMT


