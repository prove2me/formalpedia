-- Prove2me | Definitions.Def_DeletionCode_SeedLookup
-- name    : DeletionCode_SeedLookup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:00:00.6162+00:00
-- url     : https://prove2.me/theorems/d87ddc13-56c5-411d-a31e-bf6e6baba877
-- title:
--   Seed Lookup
-- statement:
--   Definitions and structural lemmas for Seed Lookup, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeedLookup.lean

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
set_option autoImplicit true
namespace DeletionCode.SeedLookup
open Windows
def Matches (x : Letters) (n k L r : ℕ) (seed : Fin k → Bool) (a : ℕ) : Prop :=
  r + k ≤ L ∧ a + L ≤ n ∧ ∀ i : Fin k, x (a + r + i.val) = seed i
instance (x : Letters) (n k L r : ℕ) (seed : Fin k → Bool) (a : ℕ) :
    Decidable (Matches x n k L r seed a) := by
  unfold Matches
  infer_instance
def lookup (x : Letters) (n k L r : ℕ) (seed : Fin k → Bool) : Option ℕ :=
  (List.range (n + 1)).find? (fun a => decide (Matches x n k L r seed a))
def recoverWindow (x : Letters) (n k L r : ℕ) (seed : Fin k → Bool) :
    Option (Fin L → Bool) :=
  (lookup x n k L r seed).map (fun a i => x (a + i.val))
end DeletionCode.SeedLookup


