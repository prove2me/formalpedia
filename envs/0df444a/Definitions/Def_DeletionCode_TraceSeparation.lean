-- Prove2me | Definitions.Def_DeletionCode_TraceSeparation
-- name    : DeletionCode_TraceSeparation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:34:38.779048+00:00
-- url     : https://prove2.me/theorems/d0793b3f-8731-435a-94c5-0c7f6932b541
-- title:
--   Trace Separation
-- statement:
--   Definitions and structural lemmas for Trace Separation, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean

import Definitions.Def_DeletionCode_FiniteConflictGraph
set_option autoImplicit true
namespace DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph
def neighborhoodLeft (L position : ℕ) : ℕ := position - (L - 1)
def neighborhoodRight (L position : ℕ) : ℕ := position + L + 1
def neighborhood (L position : ℕ) : Set ℕ :=
  Set.Ico (neighborhoodLeft L position) (neighborhoodRight L position)
end DeletionCode.TraceSeparation


