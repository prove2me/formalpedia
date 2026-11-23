-- Prove2me | Definitions.Def_VerifiedHAMT_Set
-- name    : VerifiedHAMT_Set
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:52:58.916223+00:00
-- url     : https://prove2.me/theorems/baf8a377-9886-4f71-a244-fddd15f51fc0
-- title:
--   Set
-- statement:
--   Definitions and structural lemmas for Set, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Set.lean

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace VerifiedHAMT
structure Set (α : Type u) [BEq α] [Hashable α] where
  toMap : Map α Unit
namespace Set
variable {α : Type u} [BEq α] [Hashable α]
@[inline] def ofMap (map : Map α Unit) : Set α := ⟨map⟩
@[inline] def toRaw (set : Set α) : Lean.PersistentHashSet α := ⟨set.toMap.toRaw⟩
@[inline] def ofRaw (raw : Lean.PersistentHashSet α)
    (valid : Valid raw.set) (unique : Unique raw.set.root) : Set α :=
  ⟨Map.ofRaw raw.set valid unique⟩
@[inline] def empty : Set α := ⟨∅⟩
instance : EmptyCollection (Set α) := ⟨empty⟩
instance : Inhabited (Set α) := ⟨∅⟩
@[inline] def insert [LawfulBEq α] (set : Set α) (key : α) : Set α :=
  ⟨set.toMap.insert key ()⟩
instance [LawfulBEq α] : Singleton α (Set α) := ⟨fun key => (∅ : Set α).insert key⟩
instance [LawfulBEq α] : Insert α (Set α) := ⟨fun key set => set.insert key⟩
instance [LawfulBEq α] : LawfulSingleton α (Set α) := ⟨fun _ => rfl⟩
@[inline] def ofList [LawfulBEq α] (keys : List α) : Set α :=
  keys.foldl insert ∅
@[inline] def contains (set : Set α) (key : α) : Bool := set.toMap.contains key
@[inline] def size (set : Set α) : Nat := set.toMap.size
def toList (set : Set α) : List α := set.toMap.keys
instance : Membership α (Set α) := ⟨fun set key => key ∈ set.toMap⟩
instance [LawfulBEq α] (set : Set α) (key : α) : Decidable (key ∈ set) :=
  inferInstanceAs (Decidable (key ∈ set.toMap))
end Set
end VerifiedHAMT


