-- Prove2me | Definitions.Def_LeanPool_CorlessNilpotent_Parity
-- name    : LeanPool_CorlessNilpotent_Parity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:39:53.343401+00:00
-- url     : https://prove2.me/theorems/d613067c-5f8b-4512-9789-c33b7d10382f
-- title:
--   Parity
-- statement:
--   Definitions and structural lemmas for Parity, from Marcel Blattner; maintained by LeanPool contributors's pinned Corless's nilpotent Bohemian matrix conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Parity.lean

module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Polynomial Finset
namespace Corless
def IsFolded (s : ℕ → ℤ) (n : ℕ) : Prop :=
  s (n + 1) = -s n ∧ ∀ i < n, s (2 * n + 1 - i) = s i
noncomputable def f (j : ℕ) : ℤ[X] := Dv (fun _ => 1) j
def IsSign (s : ℕ → ℤ) (m : ℕ) : Prop := ∀ i, i + 1 < m → s i = 1 ∨ s i = -1
def star (n : ℕ) : ℕ → ℤ := fun i => if i = n + 1 then -1 else 1
noncomputable def fbar (j : ℕ) : (ZMod 2)[X] := (f j).map (Int.castRingHom (ZMod 2))
end Corless


