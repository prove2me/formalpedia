-- Prove2me | solution 1 for Autoconvolutions.Blocks.ofDigits_eq_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:25.473484+00:00
-- url     : https://prove2.me/submissions/599a1f71-faed-4452-9256-ff329ea6942e

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
theorem _root_.solution {m D : ℕ} (a : Fin m → ℕ) :
    Nat.ofDigits D (List.ofFn a) = code D a := by
  induction m with
  | zero => simp [code]
  | succ m ih =>
    rw [List.ofFn_succ, Nat.ofDigits_cons, ih]
    conv_rhs => unfold code; rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, code, pow_succ, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
end Autoconvolutions.Blocks
