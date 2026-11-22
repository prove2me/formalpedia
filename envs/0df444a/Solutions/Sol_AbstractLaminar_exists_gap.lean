-- Prove2me | solution 1 for AbstractLaminar.exists_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:35:00.268406+00:00
-- url     : https://prove2.me/submissions/ee004ab4-410c-4e9f-a799-21485cf64075

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
public import Theorems.Thm_AbstractLaminar_roots_width_sum_eq
public import Theorems.Thm_AbstractLaminar_root_self_props
public import Theorems.Thm_AbstractLaminar_roots_Ioc_disjoint


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
    ∃ g, a < g ∧ g ≤ b ∧ (∀ r ∈ Roots fam a b, ¬ (fam.lo r < g ∧ g ≤ fam.hi r)) := by
  -- biUnion of root Iocs has card = ∑ widths = b-a-1 < b-a = card (Ioc a b), and is a subset.
  set B := (Roots fam a b).biUnion (fun r => Finset.Ioc (fam.lo r) (fam.hi r)) with hB
  have hsub : B ⊆ Finset.Ioc a b := by
    intro t ht
    rw [hB, Finset.mem_biUnion] at ht
    obtain ⟨r, hr, htr⟩ := ht
    rw [Finset.mem_Ioc] at htr ⊢
    obtain ⟨_, hra, hrb, _⟩ := root_self_props fam hr
    omega
  have hcardB : B.card = b - a - 1 := by
    rw [hB, Finset.card_biUnion (roots_Ioc_disjoint fam)]
    have : ∑ r ∈ Roots fam a b, (Finset.Ioc (fam.lo r) (fam.hi r)).card
        = ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) :=
      Finset.sum_congr rfl (fun r _ => Nat.card_Ioc _ _)
    rw [this, roots_width_sum_eq fam hab hsat htop]
  -- so B is a proper subset of Ioc a b, missing exactly one element.
  have hcardIoc : (Finset.Ioc a b).card = b - a := Nat.card_Ioc a b
  have hssub : B ⊂ Finset.Ioc a b := by
    rw [Finset.ssubset_iff_of_subset hsub]
    by_contra hc
    push Not at hc
    have : Finset.Ioc a b ⊆ B := hc
    have := Finset.card_le_card this
    omega
  obtain ⟨g, hgIoc, hgB⟩ := Finset.exists_of_ssubset hssub
  rw [Finset.mem_Ioc] at hgIoc
  refine ⟨g, hgIoc.1, hgIoc.2, ?_⟩
  simp_all
end AbstractLaminar
