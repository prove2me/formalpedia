-- Prove2me | solution 1 for APFB05.padded_chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-12T03:27:43.6738+00:00
-- url     : https://prove2.me/submissions/f9149ef0-a331-4d63-832b-06b3684f08b6

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
open Classical
open APFPaper1.Source

/-
APF Foundation Ledger — theorem node (Batch 1; held for the shared vocabulary by author ruling 2026-11-11)
name: APFB05.support_novel_chain_capacity_bound
title: A support-novel chain in an admissible family has at most C/epsilon members
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.27:2615-2617 (support novelty), 2836 (chain rank), 2859 (chain-rank floor theorem).
  Restates the archive bound of record APFOriginalSource.foundation_capacity_bound_infimal (ad26902d; standing
  rule 15) over the shared APFPaper1.Source vocabulary and the re-registered B05 input.
statement: At a context g, let S 0, ..., S n be finite families with S (i+1) = insert (d i) (S i), each d i
  tested and support-novel over S i, and S n admissible (some protocol serves it and its family cost is at most C g). If the
  declared input B05 (MarginalFloor) holds with floor epsilon, then n * epsilon g <= familyCost (S n) and
  n <= C g / epsilon g. Inputs consumed: B05 only. The capacity C is the function B04 speaks about; the B04
  predicate (0 <= C g) is not used. Not needed: S 0 = empty, the null-protocol zero-bill convention, attainment.
  It bounds chain length only: it does not say the family, the distinction domain or the continuation class is
  finite, and it asserts neither admissibility nor novelty.
-/

set_option autoImplicit false

namespace APFPaper1.Source

section helpers
variable {D P R Record : Type*}
variable (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)

/-- The family cost is an infimum of nonnegative reals (or of the empty set), hence nonnegative. -/
theorem familyCost_nonneg (S : Finset D) :
    0 ≤ familyCost wholeResource calibration maintained sufficient usesToRealize S := by
  unfold familyCost
  apply Real.sInf_nonneg
  rintro c ⟨p, _, rfl⟩
  exact NNReal.coe_nonneg _

/-- A protocol serving T serves every subfamily. -/
theorem familyFeasible_mono (S T : Finset D) (hST : S ⊆ T)
    (hT : familyFeasible maintained sufficient usesToRealize T) :
    familyFeasible maintained sufficient usesToRealize S := by
  obtain ⟨p, hp⟩ := hT
  exact ⟨p, fun d hd => hp d (hST hd)⟩

/-- Family cost is monotone into a feasible family. -/
theorem familyCost_mono (S T : Finset D) (hST : S ⊆ T)
    (hT : familyFeasible maintained sufficient usesToRealize T) :
    familyCost wholeResource calibration maintained sufficient usesToRealize S ≤
      familyCost wholeResource calibration maintained sufficient usesToRealize T := by
  obtain ⟨p, hp⟩ := hT
  unfold familyCost
  apply le_csInf
  · exact ⟨(calibration (wholeResource p) : ℝ), p, hp, rfl⟩
  · rintro c ⟨q, hq, rfl⟩
    apply csInf_le
    · exact ⟨0, by rintro x ⟨r, _, rfl⟩; exact NNReal.coe_nonneg _⟩
    · exact ⟨q, fun d hd => hq d (hST hd), rfl⟩

end helpers

end APFPaper1.Source

namespace APFB05

open APFPaper1.Source



end APFB05

open APFB05 in
theorem solution
    {Context : Type*} {D P R Record : Context → Type*}
    [∀ g, DecidableEq (D g)]
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (tested : (g : Context) → D g → Prop)
    (C epsilon : Context → ℝ)
    (hB05 : MarginalFloor wholeResource calibration maintained sufficient usesToRealize tested C epsilon)
    (g : Context) (n : ℕ) (S : ℕ → Finset (D g)) (d : ℕ → D g)
    (hstep : ∀ i < n, S (i + 1) = insert (d i) (S i))
    (hadm : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (S n)) :
    (∑ i ∈ Finset.range n,
        if tested g (d i) ∧ supportNovel (wholeResource g) (calibration g) (maintained g)
            (sufficient g) (usesToRealize g) (S i) (d i)
        then epsilon g else 0) ≤
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (S n) := by
  obtain ⟨_, hfloor⟩ := hB05 g
  obtain ⟨hfeas, hcost⟩ := hadm
  have hsub : ∀ i j, i ≤ j → j ≤ n → S i ⊆ S j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact Finset.Subset.refl _
    | succ j _ ih =>
      intro hj
      have hjn : j < n := Nat.lt_of_succ_le hj
      rw [hstep j hjn]
      exact (ih (Nat.le_of_lt hjn)).trans (Finset.subset_insert _ _)
  have hadmi : ∀ i, i ≤ n →
      familyAdmissible (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (C g) (S i) := by
    intro i hi
    exact ⟨familyFeasible_mono (maintained g) (sufficient g) (usesToRealize g)
        (S i) (S n) (hsub i n hi le_rfl) hfeas,
      (familyCost_mono (wholeResource g) (calibration g) (maintained g) (sufficient g)
        (usesToRealize g) (S i) (S n) (hsub i n hi le_rfl) hfeas).trans hcost⟩
  have htel : ∀ i, i ≤ n →
      (∑ j ∈ Finset.range i,
          if tested g (d j) ∧ supportNovel (wholeResource g) (calibration g) (maintained g)
              (sufficient g) (usesToRealize g) (S j) (d j)
          then epsilon g else 0) ≤
        familyCost (wholeResource g) (calibration g) (maintained g)
          (sufficient g) (usesToRealize g) (S i) := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa using familyCost_nonneg (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (S 0)
    | succ i ih =>
      intro hi
      have hin : i < n := Nat.lt_of_succ_le hi
      have h1 := ih (Nat.le_of_lt hin)
      have hmono := familyCost_mono (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (S i) (S (i + 1))
        (hsub i (i + 1) (Nat.le_succ i) hi) (hadmi (i + 1) hi).1
      rw [Finset.sum_range_succ]
      by_cases hc : tested g (d i) ∧ supportNovel (wholeResource g) (calibration g) (maintained g)
          (sufficient g) (usesToRealize g) (S i) (d i)
      · have h2 := hfloor (S i) (d i) hc.1 (hadmi i (Nat.le_of_lt hin))
          (by rw [← hstep i hin]; exact hadmi (i + 1) hi) hc.2
        rw [if_pos hc, hstep i hin]
        linarith
      · rw [if_neg hc]
        linarith
  exact htel n le_rfl
