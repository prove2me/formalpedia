-- Prove2me | solution 1 for AbstractLaminar.Sstrict_card_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:58.624145+00:00
-- url     : https://prove2.me/submissions/c96bfba7-2322-4e81-8bb9-cebebfbe046e

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
public import Theorems.Thm_AbstractLaminar_rootS_mem_Roots
public import Theorems.Thm_AbstractLaminar_fiber_eq_contained

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
    (Sstrict fam a b).card = ∑ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r) := by
  have hmaps : ∀ g ∈ Sstrict fam a b, rootS fam a b g ∈ Roots fam a b :=
    fun g hg => rootS_mem_Roots fam hg
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro r hr
  rw [fiber_eq_contained fam hr]
  rfl
end AbstractLaminar
