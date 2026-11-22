-- Prove2me | solution 1 for AbstractLaminar.crux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:25.396055+00:00
-- url     : https://prove2.me/submissions/c45c6abb-7955-45e0-a856-a656cf5726cc

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
public import Theorems.Thm_AbstractLaminar_roots_interval_disjoint
public import Theorems.Thm_AbstractLaminar_roots_Ioc_disjoint
public import Theorems.Thm_AbstractLaminar_roots_width_sum_le

set_option autoImplicit true
@[expose] public section
public section
open AbstractLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
variable {a b : ℕ}
namespace AbstractLaminar
theorem _root_.solution (hab : a < b) (htop : (topEdges fam a b).Nonempty) :
    ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) ≤ b - a - 1 := by
  by_contra hcon
  rw [not_le] at hcon
  have hle := roots_width_sum_le fam (a := a) (b := b)
  have hsum : ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) = b - a := by omega
  have hbu : (Roots fam a b).biUnion (fun r => Finset.Ioc (fam.lo r) (fam.hi r)) =
      Finset.Ioc a b := by
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      rw [Finset.mem_biUnion] at ht
      obtain ⟨r, hr, htr⟩ := ht
      rw [Finset.mem_Ioc] at htr ⊢
      obtain ⟨_, hra, hrb, _⟩ := root_self_props fam hr
      omega
    · rw [Finset.card_biUnion (roots_Ioc_disjoint fam)]
      have : ∑ r ∈ Roots fam a b, (Finset.Ioc (fam.lo r) (fam.hi r)).card
          = ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) := by
        apply Finset.sum_congr rfl; intro r _; rw [Nat.card_Ioc]
      rw [this, hsum, Nat.card_Ioc]
  obtain ⟨e0, he0⟩ := htop
  unfold topEdges at he0
  rw [mem_filter, mem_contained] at he0
  obtain ⟨⟨he0E, _, _⟩, he0lo, he0hi⟩ := he0
  have hcover : ∀ t, a < t → t ≤ b → ∃ r ∈ Roots fam a b, fam.lo r < t ∧ t ≤ fam.hi r := by
    intro t ht1 ht2
    have htmem : t ∈ Finset.Ioc a b := by rw [Finset.mem_Ioc]; exact ⟨ht1, ht2⟩
    rw [← hbu, Finset.mem_biUnion] at htmem
    obtain ⟨r, hr, htr⟩ := htmem
    rw [Finset.mem_Ioc] at htr
    exact ⟨r, hr, htr.1, htr.2⟩
  have scan : ∀ t, a < t → t ≤ b → ∀ r ∈ Roots fam a b,
      fam.lo r < t → t ≤ fam.hi r → fam.col e0 < fam.col r := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht1 ht2 r hr hrlo hrhi
      obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
      rcases Nat.lt_or_ge a (t - 1) with hprev | hprev
      · have hprev2 : t - 1 ≤ b := by omega
        obtain ⟨r'', hr'', hr''lo, hr''hi⟩ := hcover (t - 1) hprev hprev2
        have hihr'' := ih (t - 1) (by omega) hprev hprev2 r'' hr'' hr''lo hr''hi
        by_cases hrr : r = r''
        · rw [hrr]; exact hihr''
        · obtain ⟨hr''E, hr''a, hr''b, _⟩ := root_self_props fam hr''
          have hdisj := roots_interval_disjoint fam hr'' hr (fun h => hrr h.symm)
          have hseam1 : fam.hi r'' = t - 1 := by omega
          have hseam2 : fam.lo r = t - 1 := by omega
          have hseam : fam.hi r'' = fam.lo r := by omega
          have hbseam := fam.bSeam r'' hr''E r hrE hseam
          omega
      · have htea : t = a + 1 := by omega
        have hrloa : fam.lo r = a := by omega
        have hrhib : fam.hi r < b := by
          rcases hrs with h | h
          · exact absurd hrloa h
          · omega
        have hbl := fam.bLeft e0 he0E r hrE (by rw [he0lo, hrloa]) (by rw [he0hi]; exact hrhib)
        exact hbl
  obtain ⟨rb, hrb, hrblo, hrbhi⟩ := hcover b (by omega) (le_refl b)
  obtain ⟨hrbE, hrba, hrbb, hrbs⟩ := root_self_props fam hrb
  have hrbhib : fam.hi rb = b := by omega
  have hrbloa : a < fam.lo rb := by
    rcases hrbs with h | h
    · omega
    · exact absurd hrbhib h
  have hscan := scan b (by omega) (le_refl b) rb hrb hrblo hrbhi
  have hbr := fam.bRight e0 he0E rb hrbE (by rw [he0hi, hrbhib]) (by rw [he0lo]; exact hrbloa)
  omega
end AbstractLaminar
