-- Prove2me | Definitions.Def_DeletionCode_Windows
-- name    : DeletionCode_Windows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T04:57:40.282977+00:00
-- url     : https://prove2.me/theorems/d8cd8930-b71d-4104-9c33-d9eba6c11437
-- title:
--   Windows
-- statement:
--   Definitions and structural lemmas for Windows, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Windows.lean

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
set_option autoImplicit true
namespace DeletionCode.Windows
abbrev Letters := ℕ → Bool
def Agree (x : Letters) (a : ℕ) (y : Letters) (b k : ℕ) : Prop :=
  ∀ i, i < k → x (a + i) = y (b + i)
def KUnique (x : Letters) (n k : ℕ) : Prop :=
  ∀ a b, a + k ≤ n → b + k ≤ n → Agree x a x b k → a = b
def deleteAt (p : Letters) (ell : ℕ) : Letters :=
  fun i => if i < ell then p i else p (i + 1)
def insertAt (p : Letters) (ell : ℕ) (d : Bool) : Letters :=
  fun i => if i < ell then p i else if i = ell then d else p (i - 1)
def deletionSeed (k cut : ℕ) (extra : Bool) (u : Letters) : Letters :=
  fun i => if i < cut then u i else if i + 1 < k then u (i + 1) else extra
def insertionSeed (cut : ℕ) (d : Bool) (u : Letters) : Letters :=
  fun i => if i < cut then u i else if i = cut then d else u (i - 1)
end DeletionCode.Windows


