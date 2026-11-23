-- Prove2me | Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
-- name    : VerifiedHAMT_SetWithoutValArray_Operations
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T08:06:11.231144+00:00
-- url     : https://prove2.me/theorems/7c6e62e0-130d-4e97-87a1-7366f7c5ad62
-- title:
--   Operations
-- statement:
--   Definitions and structural lemmas for Operations, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Operations.lean

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_eq_true_iff
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_keyCount_empty_root
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_keyCount_insert
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_unique_empty
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_unique_insert
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_valid_empty
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_valid_insert
public import Theorems.Thm_VerifiedHAMT_unique_empty
public import Theorems.Thm_VerifiedHAMT_valid_empty

set_option autoImplicit true
@[expose] public section
@[expose] public section
structure VerifiedHAMT.SetWithoutValArray (α : Type u) [BEq α] [Hashable α]
    extends SetWithoutValArray.Raw.SizedRaw α where
  valid : SetWithoutValArray.Raw.Valid toRaw
  unique : SetWithoutValArray.Raw.Unique toRaw.root
  size_eq : size = SetWithoutValArray.Raw.keyCount toRaw.root
namespace VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
@[inline] def ofRaw (raw : Raw α) (valid : Raw.Valid raw) (unique : Raw.Unique raw.root) :
    SetWithoutValArray α :=
  ⟨⟨raw, Raw.keyCount raw.root⟩, valid, unique, rfl⟩
@[inline] def empty : SetWithoutValArray α :=
  ⟨⟨Raw.empty, 0⟩, Raw.valid_empty, Raw.unique_empty, Raw.keyCount_empty_root.symm⟩
instance : EmptyCollection (SetWithoutValArray α) := ⟨empty⟩
instance : Inhabited (SetWithoutValArray α) := ⟨∅⟩
@[inline] def insert [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    SetWithoutValArray α :=
  let result := Raw.insertSized set.toSizedRaw key
  ⟨result, Raw.valid_insert set.toRaw set.valid key,
    Raw.unique_insert set.toRaw set.valid set.unique key, by
      change (if Raw.contains set.toRaw key then set.size else set.size + 1) =
        Raw.keyCount (Raw.insert set.toRaw key).root
      rw [Raw.keyCount_insert set.toRaw set.valid set.unique, ← set.size_eq]⟩
instance [LawfulBEq α] : Singleton α (SetWithoutValArray α) := ⟨fun key => empty.insert key⟩
instance [LawfulBEq α] : Insert α (SetWithoutValArray α) := ⟨fun key set => set.insert key⟩
instance [LawfulBEq α] : LawfulSingleton α (SetWithoutValArray α) := ⟨fun _ => rfl⟩
@[inline] def ofList [LawfulBEq α] (keys : List α) : SetWithoutValArray α :=
  keys.foldl insert ∅
@[inline] def contains (set : SetWithoutValArray α) (key : α) : Bool :=
  Raw.contains set.toRaw key
def toList (set : SetWithoutValArray α) : List α := Raw.keyList set.toRaw.root
instance : Membership α (SetWithoutValArray α) := ⟨fun set key => Raw.Mem key set.toRaw⟩
theorem contains_eq_true_iff [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    set.contains key = true ↔ key ∈ set := Raw.contains_eq_true_iff set.toRaw set.valid key
instance [LawfulBEq α] (set : SetWithoutValArray α) (key : α) : Decidable (key ∈ set) :=
  decidable_of_iff (set.contains key = true) (contains_eq_true_iff set key)
end VerifiedHAMT.SetWithoutValArray


