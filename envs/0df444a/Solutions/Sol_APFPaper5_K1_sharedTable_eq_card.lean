-- Prove2me | solution 1 for APFPaper5.K1.sharedTable_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:45:55.73272+00:00
-- url     : https://prove2.me/submissions/44278a38-7281-4bfe-a679-5d4816091c1c

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_shared_count_card
title: The shared-count score is the number of distinctions two families both hold
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K1_SharedCount. Discharges the identity left open there.
consumes_inputs: none.
statement: sharedTable fam i j equals the cardinality of fam i ∩ fam j.
-/
import Definitions.Def_APFPaper5_K1_SharedCount
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
namespace APFPaper5.K1

universe u v
variable {ι : Type u} {D : Type v} [Fintype D] [DecidableEq D]

theorem sharedTable_eq_card (fam : ι → Finset D) (i j : ι) :
    sharedTable fam i j = ((fam i ∩ fam j).card : ℝ) := by
  have hterm : ∀ a : D,
      (1 : ℝ) * (ind (decide (a ∈ fam i)) * ind (decide (a ∈ fam j))) =
        if a ∈ fam i ∩ fam j then (1 : ℝ) else 0 := by
    intro a
    by_cases h1 : a ∈ fam i <;> by_cases h2 : a ∈ fam j <;> simp [ind, Finset.mem_inter, h1, h2]
  unfold sharedTable atomTable
  simp only [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

end APFPaper5.K1


universe apfNative_u apfNative_v
theorem solution :
∀ {ι : Type apfNative_u} {D : Type apfNative_v} [inst : Fintype.{apfNative_v} D]
  [inst_1 : DecidableEq.{apfNative_v + 1} D] (fam : ι → Finset.{apfNative_v} D) (i j : ι),
  @Eq.{1} Real (@APFPaper5.K1.sharedTable.{apfNative_u, apfNative_v} ι D inst inst_1 fam i j)
    (@Nat.cast.{0} Real Real.instNatCast
      (@Finset.card.{apfNative_v} D
        (@Inter.inter.{apfNative_v} (Finset.{apfNative_v} D) (@Finset.instInter.{apfNative_v} D inst_1) (fam i)
          (fam j)))) := by
  exact @APFPaper5.K1.sharedTable_eq_card
