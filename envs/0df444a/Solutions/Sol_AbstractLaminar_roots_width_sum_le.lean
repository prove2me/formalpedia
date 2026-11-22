-- Prove2me | solution 1 for AbstractLaminar.roots_width_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:49.581189+00:00
-- url     : https://prove2.me/submissions/0af76c4f-40c0-42ef-9083-2947c14dd4c1

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
public import Theorems.Thm_AbstractLaminar_root_self_props
public import Theorems.Thm_AbstractLaminar_roots_Ioc_disjoint

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
    ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) ≤ b - a := by
  have hcard : ∀ r ∈ Roots fam a b,
      fam.hi r - fam.lo r = (Finset.Ioc (fam.lo r) (fam.hi r)).card := by
    intro r _; rw [Nat.card_Ioc]
  rw [Finset.sum_congr rfl hcard]
  rw [← Finset.card_biUnion (roots_Ioc_disjoint fam)]
  rw [← Nat.card_Ioc a b]
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_biUnion] at ht
  obtain ⟨r, hr, htr⟩ := ht
  rw [Finset.mem_Ioc] at htr ⊢
  obtain ⟨_, hra, hrb, _⟩ := root_self_props fam hr
  omega
end AbstractLaminar
