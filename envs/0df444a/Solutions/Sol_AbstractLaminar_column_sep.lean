-- Prove2me | solution 1 for AbstractLaminar.column_sep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:35:36.455406+00:00
-- url     : https://prove2.me/submissions/b0a471fb-98e1-4cdd-a799-5866573c71b7

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
public import Theorems.Thm_AbstractLaminar_exists_gap
public import Theorems.Thm_AbstractLaminar_covered_of_ne_gap
public import Theorems.Thm_AbstractLaminar_seam_of_adjacent
public import Theorems.Thm_AbstractLaminar_root_self_props
public import Theorems.Thm_AbstractLaminar_roots_interval_disjoint


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
    {e0 : ι} (he0E : e0 ∈ fam.E) (he0lo : fam.lo e0 = a) (he0hi : fam.hi e0 = b) :
    ∀ r ∈ Roots fam a b, fam.col r ≠ fam.col e0 := by
  -- top edge present
  have htop : (topEdges fam a b).Nonempty := by
    refine ⟨e0, ?_⟩
    unfold topEdges; rw [Finset.mem_filter, mem_contained]
    exact ⟨⟨he0E, by omega, by omega⟩, he0lo, he0hi⟩
  obtain ⟨g, hg1, hg2, hgap⟩ := exists_gap fam hab hsat htop
  -- LEFT SCAN: roots covering levels in (a, g) have col e0 < col r.
  have scanLeft : ∀ t, a < t → t < g → ∀ r ∈ Roots fam a b,
      fam.lo r < t → t ≤ fam.hi r → fam.col e0 < fam.col r := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht1 ht2 r hr hrlo hrhi
      obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
      -- r is a left root: hi r < g.
      have hrhig : fam.hi r < g := by
        by_contra hc
        push Not at hc  -- g ≤ hi r
        exact hgap r hr ⟨by omega, hc⟩
      by_cases hlo : fam.lo r = a
      · -- bottom-most: shares bottom with e0
        have hbl := fam.bLeft e0 he0E r hrE (by rw [he0lo, hlo]) (by rw [he0hi]; omega)
        exact hbl
      · -- lo r > a; find seam predecessor covering lo r
        have hloa : a < fam.lo r := by omega
        have hlog : fam.lo r < g := by omega
        have hlone : fam.lo r ≠ g := by omega
        obtain ⟨r'', hr'', hr''lo, hr''hi⟩ :=
          covered_of_ne_gap fam htop hsat hab hg1 hg2 hgap hloa (by omega) hlone
        have hrr : r'' ≠ r := by
          intro h; rw [h] at hr''hi hr''lo; omega
        have hseam : fam.hi r'' = fam.lo r :=
          seam_of_adjacent fam hr'' hr hr''lo hr''hi (by omega) rfl
        have hih := ih (fam.lo r) (by omega) hloa hlog r'' hr'' hr''lo hr''hi
        have hbseam := fam.bSeam r'' (root_self_props fam hr'').1 r hrE hseam
        omega
  -- RIGHT SCAN: roots covering levels in (g, b] have col r < col e0. Induct on (b - t) so the
  -- inductive step can reach the seam successor (a LARGER level).
  have scanRight : ∀ n t, b - t = n → g < t → t ≤ b → ∀ r ∈ Roots fam a b,
      fam.lo r < t → t ≤ fam.hi r → fam.col r < fam.col e0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t hn ht1 ht2 r hr hrlo hrhi
      obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
      by_cases hhi : fam.hi r = b
      · -- top-most: shares top with e0
        have hbr := fam.bRight e0 he0E r hrE (by rw [he0hi, hhi]) (by rw [he0lo]; omega)
        exact hbr
      · -- hi r < b; find seam successor covering hi r + 1
        have hhib : fam.hi r < b := by omega
        have hsucc1 : g < fam.hi r + 1 := by omega
        have hsucc2 : fam.hi r + 1 ≤ b := by omega
        have hsuccne : fam.hi r + 1 ≠ g := by omega
        obtain ⟨r', hr', hr'lo, hr'hi⟩ :=
          covered_of_ne_gap fam htop hsat hab hg1 hg2 hgap (by omega) hsucc2 hsuccne
        have hrr : r' ≠ r := by
          intro h; rw [h] at hr'lo hr'hi; omega
        -- seam: hi r = lo r'
        have hseam : fam.lo r' = fam.hi r := by
          rcases roots_interval_disjoint fam hr hr' (fun h => hrr h.symm) with hd | hd
          · -- hi r ≤ lo r'; with lo r' < hi r + 1 ⇒ lo r' = hi r
            omega
          · -- hi r' ≤ lo r; but hi r + 1 ≤ hi r' and lo r < t ≤ hi r ⇒ contra
            omega
        have hih := ih (b - (fam.hi r + 1)) (by omega) (fam.hi r + 1) rfl hsucc1 hsucc2
          r' hr' hr'lo hr'hi
        have hbseam := fam.bSeam r (root_self_props fam hr).1 r'
          (root_self_props fam hr').1 hseam.symm
        omega
  -- conclude for every root
  intro r hr
  obtain ⟨hrE, hra, hrb, hrs⟩ := root_self_props fam hr
  have hlhr := fam.lh r hrE
  -- r does not span g
  have hnospan : ¬ (fam.lo r < g ∧ g ≤ fam.hi r) := hgap r hr
  rcases Nat.lt_or_ge (fam.hi r) g with hcase | hcase
  · -- left root: covers hi r ∈ (a, g)
    have h := scanLeft (fam.hi r) (by omega) hcase r hr (by omega) (le_refl _)
    omega
  · -- g ≤ hi r; since not span, g ≤ lo r; right root: covers lo r + 1 ∈ (g, b]
    have hglo : g ≤ fam.lo r := by
      by_contra hc; push Not at hc; exact hnospan ⟨hc, hcase⟩
    have h := scanRight (b - (fam.lo r + 1)) (fam.lo r + 1) rfl (by omega) (by omega) r hr
      (by omega) (by omega)
    omega
end AbstractLaminar
