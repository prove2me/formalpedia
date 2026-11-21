-- Prove2me | Definitions.Def_LeanPool_CorlessNilpotent_Path
-- name    : LeanPool_CorlessNilpotent_Path
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:39:35.838233+00:00
-- url     : https://prove2.me/theorems/9327598a-8dbc-4e8c-af79-edbc58b7dcfd
-- title:
--   Path
-- statement:
--   Definitions and structural lemmas for Path, from Marcel Blattner; maintained by LeanPool contributors's pinned Corless's nilpotent Bohemian matrix conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Path.lean

module
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Polynomial Finset
namespace Corless
noncomputable def Dv (s : ℕ → ℤ) : ℕ → ℤ[X]
  | 0 => 1
  | 1 => 1
  | (j + 2) => Dv s (j + 1) + C (s j) * X * Dv s j
end Corless


