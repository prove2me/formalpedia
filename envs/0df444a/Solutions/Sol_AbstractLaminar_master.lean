-- Prove2me | solution 1 for AbstractLaminar.master
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:33:01.256165+00:00
-- url     : https://prove2.me/submissions/41670e90-f8d0-4c34-b85c-ec0d2c0ebeb4

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
public import Theorems.Thm_AbstractLaminar_N_eq_zero_of_le
public import Theorems.Thm_AbstractLaminar_rootS_width_lt
public import Theorems.Thm_AbstractLaminar_mem_Roots
public import Theorems.Thm_AbstractLaminar_Sstrict_card_eq_sum
public import Theorems.Thm_AbstractLaminar_topEdges_card_le
public import Theorems.Thm_AbstractLaminar_N_split
public import Theorems.Thm_AbstractLaminar_roots_width_sum_le
public import Theorems.Thm_AbstractLaminar_crux

set_option autoImplicit true
@[expose] public section
public section
open AbstractLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
variable {a b : ℕ}
namespace AbstractLaminar
theorem _root_.solution (a b : ℕ) : N fam a b ≤ b - a := by
  induction hw : b - a using Nat.strongRecOn generalizing a b with
  | ind w ih =>
    rcases Nat.lt_or_ge a b with hab | hba
    · rw [N_split fam]
      rw [Sstrict_card_eq_sum fam]
      have hsub : ∑ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r)
          ≤ ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) := by
        apply Finset.sum_le_sum
        intro r hr
        have hwlt : fam.hi r - fam.lo r < w := by
          rw [mem_Roots] at hr
          have := rootS_width_lt fam hr.1
          rw [hr.2] at this
          omega
        exact ih (fam.hi r - fam.lo r) hwlt (fam.lo r) (fam.hi r) rfl
      rcases Finset.eq_empty_or_nonempty (topEdges fam a b) with htop | htop
      · rw [htop, Finset.card_empty]
        have := roots_width_sum_le fam (a := a) (b := b)
        omega
      · have hc := crux fam hab htop
        have htle := topEdges_card_le fam (a := a) (b := b)
        omega
    · rw [N_eq_zero_of_le fam hba]; omega
end AbstractLaminar
