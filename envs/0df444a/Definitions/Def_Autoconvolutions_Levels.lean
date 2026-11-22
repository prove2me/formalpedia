-- Prove2me | Definitions.Def_Autoconvolutions_Levels
-- name    : Autoconvolutions_Levels
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:47:47.572431+00:00
-- url     : https://prove2.me/theorems/54d3f6c2-049a-450e-a526-b0bf2ed3b000
-- title:
--   Levels
-- statement:
--   Definitions and structural lemmas for Levels, from Vjekoslav Kovač's pinned Sharpness for autoconvolutions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Levels.lean

module
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Real.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset Polynomial
open scoped BigOperators
namespace Autoconvolutions.Construction
noncomputable def family (P : ℕ → Polynomial ℝ) (U V : Polynomial ℝ) (n K : ℕ) :
    Polynomial ℝ :=
  ∑ i ∈ range (K + 1), U ^ (n - i) * V ^ (n + i) * P i
noncomputable def level (U V : Polynomial ℝ) (n s : ℕ) : Polynomial ℝ :=
  U ^ (2 * n - s) * V ^ (2 * n + s)
noncomputable def block (P : ℕ → Polynomial ℝ) (K s : ℕ) : Polynomial ℝ :=
  ∑ ij ∈ (antidiagonal s).filter (fun ij => ij.1 ≤ K ∧ ij.2 ≤ K), P ij.1 * P ij.2
def oddAlphabet (r : ℕ) : Finset (Fin (2*r)) :=
  univ.map (⟨fun i : Fin r => ⟨2*i.val, by omega⟩, by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega⟩ : Fin r ↪ Fin (2*r))
def evenAlphabet (r b : ℕ) (hb : b ≤ r) : Finset (Fin (2*r)) :=
  univ.map (⟨fun i : Fin b => ⟨2*i.val+1, by omega⟩, by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega⟩ : Fin b ↪ Fin (2*r))
end Autoconvolutions.Construction


