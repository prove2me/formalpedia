-- Prove2me | solution 1 for AbstractLaminar.topEdges_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:45.172972+00:00
-- url     : https://prove2.me/submissions/c2b8e965-85de-452a-8804-4781823b95dd

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
theorem _root_.solution : (topEdges fam a b).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  unfold topEdges at hx hy
  rw [mem_filter, mem_contained] at hx hy
  exact fam.inj x hx.1.1 y hy.1.1 (by rw [hx.2.1, hy.2.1]) (by rw [hx.2.2, hy.2.2])
end AbstractLaminar
