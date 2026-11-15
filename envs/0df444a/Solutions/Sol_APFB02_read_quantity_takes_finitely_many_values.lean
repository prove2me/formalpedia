-- Prove2me | solution 1 for APFB02.read_quantity_takes_finitely_many_values
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:37:50.771208+00:00
-- url     : https://prove2.me/submissions/e8ec6587-b2d2-4ce3-b482-b67ad31be842

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFB02_finite_region_has_no_continuum
title: Where finitely many distinctions tell a region's states apart, no physical quantity of one state or of two states ranges over an interval; the continuity clause as typed cannot hold there
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: ordinary mathematics on Def_APFB02_ToldApart (the clause the author stated on 2026-11-14 03:12 HST;
 named, not in FOUNDATION_INPUTS) and Def_APFPaper5_K3_Continuity (the continuity clause adopted by the author
 on 2026-11-12; named, not in FOUNDATION_INPUTS). B01 is used only in that a physical quantity is a function
 of continuation profiles. Paper 5 Supplement v7.33:217-218 (no finite witness is a proof of equality with a
 continuum) and 3670-3674 (the connectedness/continuum gate: open, structural).
consumes_inputs: none as hypotheses.
named_hypotheses: ToldApart, in the two theorems that carry "physical" in their names.
statement: (not_ranges_of_finitely_many_values) a real quantity with finitely many values does not range over
 an interval. (read_quantity_takes_finitely_many_values, relation_of_two_states_takes_finitely_many_values) a
 quantity of one state, or of two, that depends only on what finitely many distinctions read takes finitely
 many values. (overlap_of_two_states_takes_finitely_many_values) the count relation is such a quantity.
 (physical_quantity_takes_finitely_many_values, physical_relation_takes_finitely_many_values) where the
 region's distinctions tell its states apart, every quantity of one or two physical objects is such a
 quantity. (no_interval_for_a_physical_relation, continuity_clause_fails_for_a_physical_relation) so it does
 not range over an interval, and the continuity clause as typed fails for it, whatever the admissible turns.
reading: "told apart" by finitely many distinctions and "the number in a relation ranges over an interval"
 cannot both be said of one region. One of three things gives: the clause is read at a finite resolution, or
 the region has no finite number of distinctions, or the relation is not a fact about the region's states.
not_claimed: which of the three; that continuity fails physically; anything about a limit of regions.
-/
import Definitions.Def_APFPaper5_K3_Continuity
import Definitions.Def_APFPaper5_K1_AlignmentCount
import Definitions.Def_APFB02_ToldApart
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Finite.Prod

set_option autoImplicit false

theorem APFPaper5.K3.not_ranges_of_finitely_many_values {S : Type*} (rel : S → ℝ) (lo hi : ℝ)
    (hfin : (Set.range rel).Finite) : ¬ APFPaper5.K3.RangesOverInterval rel lo hi := by
  rintro ⟨hlt, hall⟩
  have hsub : Set.Icc lo hi ⊆ Set.range rel := fun t ht => by
    obtain ⟨s, hs⟩ := hall t ht.1 ht.2
    exact ⟨s, hs⟩
  exact Set.Icc_infinite hlt (hfin.subset hsub)

namespace APFB02

open APFPaper5.K1

theorem relation_of_two_states_takes_finitely_many_values {X D : Type*} [Finite D]
    (reads : D → X → Bool) (rel : X → X → ℝ)
    (hrel : ∀ x x' y y' : X, (∀ d, reads d x = reads d x') → (∀ d, reads d y = reads d y') →
      rel x y = rel x' y') :
    (Set.range (fun p : X × X => rel p.1 p.2)).Finite := by
  classical
  have key : ∃ g : Set.range (fun (x : X) (d : D) => reads d x)
      × Set.range (fun (x : X) (d : D) => reads d x) → ℝ,
      Set.range (fun p : X × X => rel p.1 p.2) ⊆ Set.range g := by
    refine ⟨fun p => rel p.1.2.choose p.2.2.choose, ?_⟩
    rintro _ ⟨⟨x, y⟩, rfl⟩
    have mx : (fun d : D => reads d x) ∈ Set.range (fun (z : X) (d : D) => reads d z) := ⟨x, rfl⟩
    have my : (fun d : D => reads d y) ∈ Set.range (fun (z : X) (d : D) => reads d z) := ⟨y, rfl⟩
    refine ⟨(⟨_, mx⟩, ⟨_, my⟩), ?_⟩
    have hx := mx.choose_spec
    have hy := my.choose_spec
    exact hrel _ _ _ _ (fun d => congrFun hx d) (fun d => congrFun hy d)
  obtain ⟨g, hg⟩ := key
  exact (Set.finite_range g).subset hg

theorem read_quantity_takes_finitely_many_values {X D : Type*} [Finite D]
    (reads : D → X → Bool) (q : X → ℝ)
    (hq : ∀ x x' : X, (∀ d, reads d x = reads d x') → q x = q x') :
    (Set.range q).Finite := by
  have h := relation_of_two_states_takes_finitely_many_values reads (fun x _ => q x)
    (fun x x' _ _ hx _ => hq x x' hx)
  refine h.subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨(x, x), rfl⟩

theorem overlap_of_two_states_takes_finitely_many_values {X D : Type*} [Fintype D]
    (reads : D → X → Bool) :
    (Set.range (fun p : X × X =>
      overlapOn Finset.univ (fun d => reads d p.1) (fun d => reads d p.2))).Finite :=
  relation_of_two_states_takes_finitely_many_values reads
    (fun x y => overlapOn Finset.univ (fun d => reads d x) (fun d => reads d y))
    (fun x x' y y' hx hy => by
      have ex : (fun d => reads d x) = fun d => reads d x' := funext hx
      have ey : (fun d => reads d y) = fun d => reads d y' := funext hy
      show overlapOn Finset.univ (fun d => reads d x) (fun d => reads d y)
        = overlapOn Finset.univ (fun d => reads d x') (fun d => reads d y')
      rw [ex, ey])

theorem physical_quantity_takes_finitely_many_values {X Q D : Type*} [Finite D]
    (Cont : X → Q → Prop) (reads : D → X → Bool) (htold : ToldApart Cont reads)
    (phi : (Q → Prop) → ℝ) :
    (Set.range (fun x : X => phi (Cont x))).Finite :=
  read_quantity_takes_finitely_many_values reads (fun x => phi (Cont x))
    (fun x x' hx => congrArg phi (htold x x' hx))

theorem physical_relation_takes_finitely_many_values {X Q D : Type*} [Finite D]
    (Cont : X → Q → Prop) (reads : D → X → Bool) (htold : ToldApart Cont reads)
    (phi : (Q → Prop) → (Q → Prop) → ℝ) :
    (Set.range (fun p : X × X => phi (Cont p.1) (Cont p.2))).Finite :=
  relation_of_two_states_takes_finitely_many_values reads (fun x y => phi (Cont x) (Cont y))
    (fun x x' y y' hx hy => by
      show phi (Cont x) (Cont y) = phi (Cont x') (Cont y')
      rw [htold x x' hx, htold y y' hy])

theorem no_interval_for_a_physical_relation {X Q D : Type*} [Finite D]
    (Cont : X → Q → Prop) (reads : D → X → Bool) (htold : ToldApart Cont reads)
    (phi : (Q → Prop) → (Q → Prop) → ℝ) (lo hi : ℝ) :
    ¬ APFPaper5.K3.RangesOverInterval (fun p : X × X => phi (Cont p.1) (Cont p.2)) lo hi :=
  APFPaper5.K3.not_ranges_of_finitely_many_values _ lo hi
    (physical_relation_takes_finitely_many_values Cont reads htold phi)

theorem continuity_clause_fails_for_a_physical_relation {X Q D : Type*} [Finite D]
    (Cont : X → Q → Prop) (reads : D → X → Bool) (htold : ToldApart Cont reads)
    (phi : (Q → Prop) → (Q → Prop) → ℝ) (lo hi : ℝ) (Adm : Set (X × X → X × X)) :
    ¬ APFPaper5.K3.Continuity (fun p : X × X => phi (Cont p.1) (Cont p.2)) lo hi Adm :=
  fun h => no_interval_for_a_physical_relation Cont reads htold phi lo hi h.1

end APFB02


universe apfNative_u_1 apfNative_u_2
theorem solution :
∀ {X : Type apfNative_u_1} {D : Type apfNative_u_2} [Finite.{apfNative_u_2 + 1} D] (reads : D → X → Bool) (q : X → Real)
  (hq : ∀ (x x' : X), (∀ (d : D), @Eq.{1} Bool (reads d x) (reads d x')) → @Eq.{1} Real (q x) (q x')),
  @Set.Finite.{0} Real (@Set.range.{0, apfNative_u_1 + 1} Real X q) := by
  exact @APFB02.read_quantity_takes_finitely_many_values
