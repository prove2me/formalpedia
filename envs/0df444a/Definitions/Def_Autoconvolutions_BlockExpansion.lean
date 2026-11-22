-- Prove2me | Definitions.Def_Autoconvolutions_BlockExpansion
-- name    : Autoconvolutions_BlockExpansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:48:06.467141+00:00
-- url     : https://prove2.me/theorems/af903f9d-2719-4771-b1f6-91da3dc14cb0
-- title:
--   Block Expansion
-- statement:
--   Definitions and structural lemmas for Block Expansion, from Vjekoslav Kovač's pinned Sharpness for autoconvolutions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockExpansion.lean

module
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset Polynomial
open scoped BigOperators
namespace Autoconvolutions.Blocks
noncomputable def gen {m : ℕ} (D : ℕ) (I : Finset (Fin m)) : Polynomial ℝ :=
  ∑ i ∈ I, X ^ (D * D ^ i.val)
end Autoconvolutions.Blocks


