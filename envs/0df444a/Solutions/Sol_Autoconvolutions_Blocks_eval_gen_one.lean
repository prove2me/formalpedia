-- Prove2me | solution 1 for Autoconvolutions.Blocks.eval_gen_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:48:35.797626+00:00
-- url     : https://prove2.me/submissions/10f25724-2342-464a-a273-fb71c64926c1

module
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_BlockExpansion

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Blocks
namespace Autoconvolutions.Blocks
theorem _root_.solution {m : ℕ} (D : ℕ) (I : Finset (Fin m)) :
    (gen D I).eval 1 = (I.card : ℝ) := by
  simp [gen, Polynomial.eval_finsetSum]
end Autoconvolutions.Blocks
