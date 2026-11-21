-- Prove2me | Definitions.Def_LeanPool_CorlessNilpotent_Main
-- name    : LeanPool_CorlessNilpotent_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:40:22.498638+00:00
-- url     : https://prove2.me/theorems/cf7d3aae-3d8f-4cc1-8940-c4096ce91894
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Marcel Blattner; maintained by LeanPool contributors's pinned Corless's nilpotent Bohemian matrix conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Polynomial Finset
namespace Corless
def hyb (s t : ℕ → ℤ) (j : ℕ) : ℕ → ℤ := fun i => if i < j then s i else t i
def Fam : ℕ → (ℕ → ℤ) → Prop
  | 0, _ => True
  | k + 1, s => IsFolded s (2 ^ (k + 1) - 2) ∧ Fam k s
end Corless


