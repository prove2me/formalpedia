-- Prove2me | solution 1 for AbstractLaminar.covered_of_ne_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:34:59.806041+00:00
-- url     : https://prove2.me/submissions/4a1c9d35-2962-4587-9edd-0b526b0dd18a

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
theorem _root_.solution {a b g : ℕ} (htop : (topEdges fam a b).Nonempty)
    (hsat : N fam a b = b - a) (hab : a < b)
    (hg1 : a < g) (hg2 : g ≤ b)
    (hgap : ∀ r ∈ Roots fam a b, ¬ (fam.lo r < g ∧ g ≤ fam.hi r))
    {t : ℕ} (ht1 : a < t) (ht2 : t ≤ b) (htne : t ≠ g) :
    ∃ r ∈ Roots fam a b, fam.lo r < t ∧ t ≤ fam.hi r := by
  set B := (Roots fam a b).biUnion (fun r => Finset.Ioc (fam.lo r) (fam.hi r)) with hB
  have hsub : B ⊆ Finset.Ioc a b := by
    intro s hs
    rw [hB, Finset.mem_biUnion] at hs
    obtain ⟨r, hr, hsr⟩ := hs
    rw [Finset.mem_Ioc] at hsr ⊢
    obtain ⟨_, hra, hrb, _⟩ := root_self_props fam hr
    omega
  have hcardB : B.card = b - a - 1 := by
    rw [hB, Finset.card_biUnion (roots_Ioc_disjoint fam)]
    have : ∑ r ∈ Roots fam a b, (Finset.Ioc (fam.lo r) (fam.hi r)).card
        = ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) :=
      Finset.sum_congr rfl (fun r _ => Nat.card_Ioc _ _)
    rw [this, roots_width_sum_eq fam hab hsat htop]
  have hgnotB : g ∉ B := by
    simp_all
  have hgIoc : g ∈ Finset.Ioc a b := by rw [Finset.mem_Ioc]; exact ⟨hg1, hg2⟩
  -- insert g B ⊆ Ioc a b with card (b-a-1)+1 = b-a = card Ioc ⇒ insert g B = Ioc a b.
  have hins_sub : insert g B ⊆ Finset.Ioc a b := Finset.insert_subset hgIoc hsub
  have hins_card : (insert g B).card = b - a := by
    rw [Finset.card_insert_of_notMem hgnotB, hcardB]
    have hbpos : 1 ≤ b - a := by omega
    omega
  have heq : insert g B = Finset.Ioc a b :=
    Finset.eq_of_subset_of_card_le hins_sub (by rw [hins_card, Nat.card_Ioc])
  -- t ∈ Ioc a b, t ≠ g ⇒ t ∈ B
  have htIoc : t ∈ Finset.Ioc a b := by rw [Finset.mem_Ioc]; exact ⟨ht1, ht2⟩
  rw [← heq, Finset.mem_insert] at htIoc
  simp_all
end AbstractLaminar
