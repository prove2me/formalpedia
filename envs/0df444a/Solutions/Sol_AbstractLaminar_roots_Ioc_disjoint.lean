-- Prove2me | solution 1 for AbstractLaminar.roots_Ioc_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:10.326235+00:00
-- url     : https://prove2.me/submissions/fc33429f-1d5c-4dea-9ed3-1f532e27609f

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
public import Theorems.Thm_AbstractLaminar_roots_interval_disjoint

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
    (Roots fam a b : Set ι).PairwiseDisjoint (fun r => Finset.Ioc (fam.lo r) (fam.hi r)) := by
  intro r hr r' hr' hne
  simp only [Finset.disjoint_left, Finset.mem_Ioc]
  rintro t ⟨ht1, ht2⟩ ⟨ht3, ht4⟩
  rcases roots_interval_disjoint fam hr hr' hne with h | h <;> omega
end AbstractLaminar
