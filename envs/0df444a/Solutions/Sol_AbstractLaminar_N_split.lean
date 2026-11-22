-- Prove2me | solution 1 for AbstractLaminar.N_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:45.739625+00:00
-- url     : https://prove2.me/submissions/7880e197-1183-4370-8378-f5efaebd3f58

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Theorems.Thm_AbstractLaminar_Sstrict_eq_filter_not

set_option autoImplicit true
@[expose] public section
public section
open AbstractLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
variable {a b : ℕ}
namespace AbstractLaminar
theorem _root_.solution : N fam a b = (topEdges fam a b).card + (Sstrict fam a b).card := by
  rw [Sstrict_eq_filter_not]
  unfold N topEdges
  exact (Finset.card_filter_add_card_filter_not (s := contained fam a b)
    (fun e => fam.lo e = a ∧ fam.hi e = b)).symm
end AbstractLaminar
