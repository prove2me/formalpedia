-- Prove2me | solution 1 for AbstractLaminar.roots_width_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:34:23.022939+00:00
-- url     : https://prove2.me/submissions/66ae016e-29d2-46bb-afad-27c67b8157ad

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Theorems.Thm_AbstractLaminar_root_saturated
public import Theorems.Thm_AbstractLaminar_N_split
public import Theorems.Thm_AbstractLaminar_Sstrict_card_eq_sum
public import Theorems.Thm_AbstractLaminar_topEdges_card_le


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open AbstractLaminar
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
namespace AbstractLaminar
theorem _root_.solution {a b : ℕ} (hab : a < b) (hsat : N fam a b = b - a)
    (htop : (topEdges fam a b).Nonempty) :
    ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) = b - a - 1 := by
  -- each root saturated ⇒ ∑ N(lo,hi) = ∑ widths.
  have hrsat := root_saturated fam hsat
  have hcongr : (∑ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r))
      = ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) :=
    Finset.sum_congr rfl (fun r hr => hrsat r hr)
  have hSstrict := Sstrict_card_eq_sum fam (a := a) (b := b)
  have hNsplit := N_split fam (a := a) (b := b)
  have htone : (topEdges fam a b).card = 1 :=
    le_antisymm (topEdges_card_le fam) (Finset.card_pos.mpr htop)
  -- N = 1 + #Sstrict = 1 + ∑ widths; N = b - a; so ∑ widths = b - a - 1
  rw [htone] at hNsplit
  rw [hSstrict, hcongr] at hNsplit
  omega
end AbstractLaminar
