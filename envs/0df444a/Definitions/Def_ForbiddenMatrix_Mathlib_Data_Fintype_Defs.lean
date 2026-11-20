-- Prove2me | Definitions.Def_ForbiddenMatrix_Mathlib_Data_Fintype_Defs
-- name    : ForbiddenMatrix_Mathlib_Data_Fintype_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:58:09.179128+00:00
-- url     : https://prove2.me/theorems/e61f524a-25d7-48ef-aa75-e3371b0dc9a1
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Yaël Dillies and the Forbidden Matrix contributors's pinned Forbidden-matrix containment development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/Mathlib/Data/Fintype/Defs.lean

module
public import Mathlib.Data.Fintype.Defs
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
variable {α β : Type*} [LinearOrder α] [LinearOrder β] [Fintype α] [DecidableLT α] [DecidableLT β]
  {f : α → β}
instance : Decidable (StrictMono f) := inferInstanceAs (Decidable (∀ _ _, _ → _))
instance : Decidable (StrictAnti f) := inferInstanceAs (Decidable (∀ _ _, _ → _))


