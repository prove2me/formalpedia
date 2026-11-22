-- Prove2me | solution 1 for Autoconvolutions.Flat.weight_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:06.974992+00:00
-- url     : https://prove2.me/submissions/284f5eed-c234-46b4-8b05-1289f6272761

module
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_Flat

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open Autoconvolutions Autoconvolutions.Flat
noncomputable section
namespace Autoconvolutions.Flat
theorem _root_.solution (n : ℕ) : 0 < weight n := by
  exact div_pos (by exact_mod_cast Nat.centralBinom_pos n) (by positivity)
end Autoconvolutions.Flat
