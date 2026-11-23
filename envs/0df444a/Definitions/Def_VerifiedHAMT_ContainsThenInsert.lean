-- Prove2me | Definitions.Def_VerifiedHAMT_ContainsThenInsert
-- name    : VerifiedHAMT_ContainsThenInsert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:33:31.129001+00:00
-- url     : https://prove2.me/theorems/07f58abe-1987-4470-9254-0aa67c9e772e
-- title:
--   Contains Then Insert
-- statement:
--   Definitions and structural lemmas for Contains Then Insert, from verse-lab/VerifiedHAMT contributors (see pinned LICENSE and source headers)'s pinned Verified hash array mapped tries development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/ContainsThenInsert.lean

module
public import Definitions.Def_VerifiedHAMT_InsertSized
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace VerifiedHAMT
variable {α : Type u} {β : Type v}
def containsThenInsertImpl [BEq α] [Hashable α] (map : Lean.PersistentHashMap α β)
    (key : α) (value : β) : Bool × Lean.PersistentHashMap α β :=
  let result := insertSizedImpl ⟨map, 0⟩ key value
  (result.size == 0, result.toRaw)
def containsThenInsert [BEq α] [Hashable α] (map : Lean.PersistentHashMap α β)
    (key : α) (value : β) : Bool × Lean.PersistentHashMap α β :=
  (contains map key, insert map key value)
end VerifiedHAMT


