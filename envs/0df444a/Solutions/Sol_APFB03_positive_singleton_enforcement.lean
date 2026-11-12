-- Prove2me | solution 1 for APFB03.positive_singleton_enforcement
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-12T03:26:09.176004+00:00
-- url     : https://prove2.me/submissions/a69c5e53-f735-4abf-9533-cb9ffd81e966

import Definitions.Def_APFPaper1_CostLedger
import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APFPaper1_LedgerOfSource
import Definitions.Def_APF_B03_DeclaredInput_r2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_APFPaper1_Foundation_cost_ofSource
set_option autoImplicit false
open Classical
open APFPaper1.Source

/-
APF Foundation Ledger — theorem node (Batch 2). First theorems consuming the declared input B03.
name: APFB03.positive_singleton_enforcement
title: Under B03 every singleton task is feasible and every protocol realizing it has a positive bill
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.27:1744-1757 (physical distinction; enforcement cost; "requires a nonempty class and
  0 < kappa(d) < infinity"), 2880-2883 (empty protocol at zero cost). Restates the archive theorem
  APFOriginalProcess.positive_nonnull_enforcement (e6b2c5c0) over the shared APFPaper1.Source vocabulary and the
  re-registered B03 input; the ledger form uses the Batch 1 bridge cost_ofSource.
statement: Let B03 hold (B03TaskCost). Then at every context g and for every tested distinction d of D g:
  (1) singleton_feasible: some protocol serves {d}. B03 is stated as positivity of a real infimum, and the real
      infimum of an empty set is 0, so positivity already forces the serving class to be nonempty; this theorem
      makes that consequence visible rather than leaving it in the encoding.
  (2) positive_nonnull_enforcement: every protocol p that realizes d from its own maintained sufficient support has
      a strictly positive calibrated whole-resource bill, and p differs from any protocol whose bill is zero.
  (3) positive_singleton_cost_ledger: for a designated null protocol p0 of zero bill, the CostLedger infimal cost of
      {d} on Ledger.ofSource is strictly positive.
  Inputs consumed: B03 only. Nothing is asserted about a uniform floor across tasks, about attainment, or about any
  change of physical state.
-/

set_option autoImplicit false

namespace APFB03

open APFPaper1.Source

theorem singleton_feasible
    {Context : Type*} {D P R Record : Context → Type*}
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (hB03 : B03TaskCost wholeResource calibration maintained sufficient usesToRealize)
    (g : Context) (d : D g) :
    familyFeasible (maintained g) (sufficient g) (usesToRealize g) {d} := by
  have h := hB03 g d
  by_contra hne
  have hzero : familyCost (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) {d} = 0 := by
    unfold familyCost
    convert Real.sInf_empty
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨p, hp, _⟩
    exact hne ⟨p, hp⟩
  linarith

theorem positive_nonnull_enforcement
    {Context : Type*} {D P R Record : Context → Type*}
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (hB03 : B03TaskCost wholeResource calibration maintained sufficient usesToRealize)
    (g : Context) (d : D g) (p : P g)
    (hp : ∃ sigma : Set (Record g),
      sigma ⊆ maintained g p ∧ sufficient g p sigma d ∧ usesToRealize g p d sigma) :
    0 < (calibration g (wholeResource g p) : ℝ) ∧
      ∀ p0 : P g, calibration g (wholeResource g p0) = 0 → p ≠ p0 := by
  have h := hB03 g d
  have hle : familyCost (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) {d} ≤ (calibration g (wholeResource g p) : ℝ) := by
    unfold familyCost
    apply csInf_le
    · exact ⟨0, by rintro x ⟨q, _, rfl⟩; exact NNReal.coe_nonneg _⟩
    · refine ⟨p, ?_, rfl⟩
      intro e he
      rw [Finset.mem_singleton] at he
      subst he
      exact hp
  have hpos : 0 < (calibration g (wholeResource g p) : ℝ) := by linarith
  refine ⟨hpos, ?_⟩
  intro p0 hnull hpp
  rw [hpp, hnull] at hpos
  simp at hpos

theorem positive_singleton_cost_ledger
    {Context : Type*} {D P R Record : Context → Type*}
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (hB03 : B03TaskCost wholeResource calibration maintained sufficient usesToRealize)
    (g : Context) (p0 : P g) (hnull : calibration g (wholeResource g p0) = 0) (d : D g) :
    0 < APFPaper1.Foundation.cost
      (APFPaper1.Foundation.Ledger.ofSource p0 (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g)) {d} := by
  rw [APFPaper1.Foundation.cost_ofSource p0 (wholeResource g) (calibration g) (maintained g)
    (sufficient g) (usesToRealize g) hnull]
  exact hB03 g d



end APFB03

open APFB03 in
theorem solution
    {Context : Type*} {D P R Record : Context → Type*}
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (hB03 : B03TaskCost wholeResource calibration maintained sufficient usesToRealize)
    (g : Context) (d : D g) :
    familyFeasible (maintained g) (sufficient g) (usesToRealize g) {d} ∧
      (∀ p : P g,
        (∃ sigma : Set (Record g), sigma ⊆ maintained g p ∧
          sufficient g p sigma d ∧ usesToRealize g p d sigma) →
        0 < (calibration g (wholeResource g p) : ℝ) ∧
          ∀ p0 : P g, calibration g (wholeResource g p0) = 0 → p ≠ p0) ∧
      (∀ p0 : P g, calibration g (wholeResource g p0) = 0 →
        0 < APFPaper1.Foundation.cost
          (APFPaper1.Foundation.Ledger.ofSource p0 (wholeResource g) (calibration g)
            (maintained g) (sufficient g) (usesToRealize g)) {d}) := by
  refine ⟨singleton_feasible wholeResource calibration maintained sufficient usesToRealize
    hB03 g d, ?_, ?_⟩
  · intro p hp
    exact positive_nonnull_enforcement wholeResource calibration maintained sufficient
      usesToRealize hB03 g d p hp
  · intro p0 hnull
    exact positive_singleton_cost_ledger wholeResource calibration maintained sufficient
      usesToRealize hB03 g p0 hnull d
