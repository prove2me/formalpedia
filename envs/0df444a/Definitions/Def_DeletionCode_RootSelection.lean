-- Prove2me | Definitions.Def_DeletionCode_RootSelection
-- name    : DeletionCode_RootSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T04:58:44.714944+00:00
-- url     : https://prove2.me/theorems/5a73c1c3-099d-47e8-a7d0-a47f3a2ae5df
-- title:
--   Root Selection
-- statement:
--   Definitions and structural lemmas for Root Selection, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RootSelection.lean

import Definitions.Def_DeletionCode_WordPaths
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Relation
set_option autoImplicit true
namespace DeletionCode.RootSelection
open Windows
structure Family (B : Type*) where
  rank : B → ℕ
  path : B → Bool → Letters
  extra : B → Bool → ℕ
namespace Family
def Generating {B : Type*} (F : Family B) (x : Letters) (n L : ℕ) : Prop :=
  ∀ b i, i ≤ F.extra b false →
    WordPaths.Occurs x n (F.path b false) i L ∨
      ∃ a side j, F.rank a < F.rank b ∧ j ≤ F.extra a side ∧
        Agree (F.path b false) i (F.path a side) j L
def Adjacent {B : Type*} (F : Family B) (L : ℕ) (a b : B) : Prop :=
  ∃ sideA sideB i j,
    i ≤ F.extra a sideA + 1 ∧ j ≤ F.extra b sideB + 1 ∧
    i + (L - 1) ≤ L + F.extra a sideA ∧
    j + (L - 1) ≤ L + F.extra b sideB ∧
    Agree (F.path a sideA) i (F.path b sideB) j (L - 1)
def Connected {B : Type*} (F : Family B) (L : ℕ) : B → B → Prop :=
  Relation.EqvGen (F.Adjacent L)
end Family
end DeletionCode.RootSelection


