-- Prove2me | solution 1 for Autoconvolutions.Blocks.code_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:25.993619+00:00
-- url     : https://prove2.me/submissions/51a0b193-091b-497e-9e61-9b445de02bbe

module
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_BlockKeys

set_option autoImplicit true
@[expose] public section
public section
open Autoconvolutions Autoconvolutions.Blocks
open Finset
namespace Autoconvolutions.Blocks
theorem _root_.solution {m D : ℕ} (a b : Fin m → ℕ) :
    code D (fun i => a i + b i) = code D a + code D b := by
  simp [code, add_mul, Finset.sum_add_distrib]
end Autoconvolutions.Blocks
