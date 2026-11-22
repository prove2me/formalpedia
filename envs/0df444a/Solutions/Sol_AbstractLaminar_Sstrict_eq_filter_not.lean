-- Prove2me | solution 1 for AbstractLaminar.Sstrict_eq_filter_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:55.860114+00:00
-- url     : https://prove2.me/submissions/5feb3d9f-0117-4cd1-ae61-ff9d3c564f0c

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

set_option autoImplicit true
@[expose] public section
public section
open AbstractLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
variable {a b : ℕ}
namespace AbstractLaminar
theorem _root_.solution :
    Sstrict fam a b = (contained fam a b).filter (fun e => ¬ (fam.lo e = a ∧ fam.hi e = b)) := by
  unfold Sstrict
  apply Finset.filter_congr
  intro e _
  unfold IsStrict
  constructor
  · rintro (h | h) ⟨h1, h2⟩ <;> [exact h h1; exact h h2]
  · intro h
    rw [not_and_or] at h
    exact h
end AbstractLaminar
