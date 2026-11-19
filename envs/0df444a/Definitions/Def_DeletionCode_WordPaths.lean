-- Prove2me | Definitions.Def_DeletionCode_WordPaths
-- name    : DeletionCode_WordPaths
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T04:58:27.445611+00:00
-- url     : https://prove2.me/theorems/d6603807-7bfc-498a-814f-8244be2a1f1b
-- title:
--   Word Paths
-- statement:
--   Definitions and structural lemmas for Word Paths, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WordPaths.lean

import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
namespace DeletionCode.WordPaths
open Windows
def Occurs (x : Letters) (n : ℕ) (p : Letters) (i L : ℕ) : Prop :=
  ∃ a, a + L ≤ n ∧ Agree x a p i L
end DeletionCode.WordPaths


