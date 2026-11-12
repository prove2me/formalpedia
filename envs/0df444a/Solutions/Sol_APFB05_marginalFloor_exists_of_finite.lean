-- Prove2me | solution 1 for APFB05.marginalFloor_exists_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-12T03:29:21.216477+00:00
-- url     : https://prove2.me/submissions/3b5b1054-4398-4130-baf2-fb99be93fe96

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
set_option autoImplicit false
open Classical
open APFPaper1.Source

/-
APF Foundation Ledger — theorem node (Batch 2). A theorem ABOUT the declared input B05; it consumes no input.
name: APFB05.marginalFloor_exists_of_finite
title: On finite distinction domains a marginal floor exists without assuming it
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.27:1807-1818 ("a nonempty finite domain of positive increments has a positive
  minimum"), 1560-1567 (finite tested regime: the floor is not an additional postulate), 2615-2617 (support
  novelty), 2650-2652 (the infinite family with costs 1/n, where the hypothesis has teeth).
statement: (1) supportNovel_positive_gap: if insert d S is feasible and d is support-novel over S, then
  familyCost S < familyCost (insert d S). (2) exists_floor_of_finite: if the distinction type is finite, there is
  an epsilon > 0 below every increment familyCost (insert d S) - familyCost S over feasible support-novel pairs.
  (3) marginalFloor_exists_of_finite: if every D g is finite, then for every tested predicate and every capacity
  function C there exists an epsilon for which MarginalFloor holds. So on finite domains B05 is a consequence of
  the cost definitions alone, and it is a genuine assumption only for a context with infinitely many tested
  distinctions or when a particular value of epsilon is asserted. The theorem gives existence only: no value of
  epsilon, and no uniformity across contexts.
-/

set_option autoImplicit false

namespace APFPaper1.Source

theorem supportNovel_positive_gap {D P R Record : Type*} [DecidableEq D]
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop)
    (S : Finset D) (d : D)
    (hf : familyFeasible maintained sufficient usesToRealize (insert d S))
    (hn : supportNovel wholeResource calibration maintained sufficient usesToRealize S d) :
    familyCost wholeResource calibration maintained sufficient usesToRealize S <
      familyCost wholeResource calibration maintained sufficient usesToRealize (insert d S) := by
  obtain ⟨η, hη, hn⟩ := hn
  obtain ⟨p, hp⟩ := hf
  have hbound : familyCost wholeResource calibration maintained sufficient usesToRealize S + η ≤
      familyCost wholeResource calibration maintained sufficient usesToRealize (insert d S) := by
    apply le_csInf
    · exact ⟨(calibration (wholeResource p) : ℝ), p, hp, rfl⟩
    · rintro c ⟨q, hq, rfl⟩
      by_contra! hlt
      obtain ⟨σ, h1, h2, _⟩ := hq d (Finset.mem_insert_self d S)
      exact hn q (fun e he => hq e (Finset.mem_insert_of_mem he)) (le_of_lt hlt) ⟨σ, h1, h2⟩
  linarith

/-- A finite set of positive reals has a positive lower bound. Ordinary mathematics. -/
theorem pos_lower_bound_of_finite (A : Set ℝ) (hA : A.Finite) (hpos : ∀ x ∈ A, 0 < x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ A, ε ≤ x := by
  by_cases hne : A.Nonempty
  · have hne' : hA.toFinset.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, hA.mem_toFinset.mpr hx⟩
    refine ⟨hA.toFinset.min' hne', hpos _ (hA.mem_toFinset.mp (Finset.min'_mem _ _)), ?_⟩
    intro x hx
    exact Finset.min'_le _ x (hA.mem_toFinset.mpr hx)
  · refine ⟨1, one_pos, ?_⟩
    intro x hx
    exact absurd ⟨x, hx⟩ hne

theorem exists_floor_of_finite {D P R Record : Type*} [DecidableEq D] [Finite D]
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (S : Finset D) (d : D),
      familyFeasible maintained sufficient usesToRealize (insert d S) →
      supportNovel wholeResource calibration maintained sufficient usesToRealize S d →
      ε ≤ familyCost wholeResource calibration maintained sufficient usesToRealize (insert d S) -
        familyCost wholeResource calibration maintained sufficient usesToRealize S := by
  have : Fintype D := Fintype.ofFinite D
  obtain ⟨ε, hε, hle⟩ := pos_lower_bound_of_finite
    {y : ℝ | ∃ x : Finset D × D,
      (familyFeasible maintained sufficient usesToRealize (insert x.2 x.1) ∧
        supportNovel wholeResource calibration maintained sufficient usesToRealize x.1 x.2) ∧
      familyCost wholeResource calibration maintained sufficient usesToRealize (insert x.2 x.1) -
        familyCost wholeResource calibration maintained sufficient usesToRealize x.1 = y}
    ((Set.finite_range (fun x : Finset D × D =>
        familyCost wholeResource calibration maintained sufficient usesToRealize (insert x.2 x.1) -
          familyCost wholeResource calibration maintained sufficient usesToRealize x.1)).subset
      (by rintro y ⟨x, _, rfl⟩; exact ⟨x, rfl⟩))
    (by
      rintro y ⟨x, ⟨hf, hn⟩, rfl⟩
      have := supportNovel_positive_gap wholeResource calibration maintained sufficient
        usesToRealize x.1 x.2 hf hn
      linarith)
  exact ⟨ε, hε, fun S d hf hn => hle _ ⟨(S, d), ⟨hf, hn⟩, rfl⟩⟩

end APFPaper1.Source

namespace APFB05

open APFPaper1.Source



end APFB05

open APFB05 in
theorem solution
    {Context : Type*} {D P R Record : Context → Type*}
    [∀ g, DecidableEq (D g)] [∀ g, Finite (D g)]
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (tested : (g : Context) → D g → Prop)
    (C : Context → ℝ) :
    ∃ epsilon : Context → ℝ,
      MarginalFloor wholeResource calibration maintained sufficient usesToRealize tested C epsilon := by
  choose epsilon hε hfloor using fun g =>
    exists_floor_of_finite (wholeResource g) (calibration g) (maintained g) (sufficient g)
      (usesToRealize g)
  exact ⟨epsilon, fun g => ⟨hε g, fun S d _ _ hadm hn => hfloor g S d hadm.1 hn⟩⟩
