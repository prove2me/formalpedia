-- Prove2me | Definitions.Def_VerifiedHAMT_Map
-- name    : VerifiedHAMT_Map
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:52:28.159974+00:00
-- url     : https://prove2.me/theorems/21ca12ac-4d71-4bfb-b8f3-a1023b673f1a
-- title:
--   Map
-- statement:
--   Definitions and structural lemmas for Map, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Theorems.Thm_VerifiedHAMT_contains_eq_true_iff
public import Theorems.Thm_VerifiedHAMT_keyCount_empty_root
public import Theorems.Thm_VerifiedHAMT_keyCount_insert
public import Theorems.Thm_VerifiedHAMT_unique_empty
public import Theorems.Thm_VerifiedHAMT_unique_insert
public import Theorems.Thm_VerifiedHAMT_valid_empty
public import Theorems.Thm_VerifiedHAMT_valid_insert

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace VerifiedHAMT
structure Map (α : Type u) (β : Type v) [BEq α] [Hashable α] extends SizedRaw α β where
  /-- Every stored key follows its hash route. -/
  valid : Valid toRaw
  /-- Keys are unique, so overwriting has the usual map semantics. -/
  unique : Unique toRaw.root
  /-- `size` counts the keys stored in the native tree. -/
  size_eq : size = keyCount toRaw.root
namespace Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
@[inline] def ofRaw (raw : Lean.PersistentHashMap α β)
    (valid : Valid raw) (unique : Unique raw.root) : Map α β :=
  ⟨⟨raw, keyCount raw.root⟩, valid, unique, rfl⟩
theorem unique_empty_root : Unique (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β).root :=
  unique_empty
@[inline] def empty : Map α β :=
  ⟨⟨Lean.PersistentHashMap.empty, 0⟩, valid_empty, unique_empty_root, keyCount_empty_root.symm⟩
instance : EmptyCollection (Map α β) := ⟨empty⟩
instance : Inhabited (Map α β) := ⟨∅⟩
@[inline] def insert [LawfulBEq α] (map : Map α β) (key : α) (value : β) : Map α β :=
  let result := VerifiedHAMT.insertSized map.toSizedRaw key value
  ⟨result,
    valid_insert map.toRaw map.valid key value,
    unique_insert map.toRaw map.valid map.unique key value,
    by
      change (if VerifiedHAMT.contains map.toRaw key then map.size else map.size + 1) =
        keyCount (VerifiedHAMT.insert map.toRaw key value).root
      rw [keyCount_insert map.toRaw map.valid map.unique, ← map.size_eq]⟩
instance [LawfulBEq α] : Singleton (α × β) (Map α β) :=
  ⟨fun kv => (∅ : Map α β).insert kv.1 kv.2⟩
instance [LawfulBEq α] : Insert (α × β) (Map α β) :=
  ⟨fun kv map => map.insert kv.1 kv.2⟩
instance [LawfulBEq α] : LawfulSingleton (α × β) (Map α β) := ⟨fun _ => rfl⟩
@[inline] def ofList [LawfulBEq α] (bindings : List (α × β)) : Map α β :=
  bindings.foldl (fun map kv => map.insert kv.1 kv.2) ∅
@[inline] def contains (map : Map α β) (key : α) : Bool :=
  VerifiedHAMT.contains map.toRaw key
@[inline] def find? (map : Map α β) (key : α) : Option β :=
  VerifiedHAMT.find? map.toRaw key
@[inline] def findD (map : Map α β) (key : α) (fallback : β) : β :=
  VerifiedHAMT.findD map.toRaw key fallback
instance : Membership α (Map α β) := ⟨fun map key => VerifiedHAMT.Mem key map.toRaw⟩
def MapsTo (map : Map α β) (key : α) (value : β) : Prop :=
  VerifiedHAMT.MapsTo key value map.toRaw
def keys (map : Map α β) : List α := keyList map.toRaw.root
theorem contains_eq_true_iff [LawfulBEq α] (map : Map α β) (key : α) :
    map.contains key = true ↔ key ∈ map :=
  VerifiedHAMT.contains_eq_true_iff map.toRaw map.valid key
instance [LawfulBEq α] (map : Map α β) (key : α) : Decidable (key ∈ map) :=
  decidable_of_iff (map.contains key = true) (contains_eq_true_iff map key)
end Map
end VerifiedHAMT


