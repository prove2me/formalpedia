-- Prove2me | solution 1 for APFPaper1.Source.familyCost_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:06:06.105344+00:00
-- url     : https://prove2.me/submissions/5e3bda7c-7fd0-4f13-9ba3-61e92e35eac5

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_familyCost_mono
title: The ledger's family cost is nonnegative and does not fall when a feasible family grows
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFPaper1_FamilyCost (Paper 1 Supplement v9.28:1763-1776). Codebank apf/delta_calculus.py records
 kappa as subset-monotone. The same step sits inside APFB05.familyAdmissible_of_subset; it is stated here on
 its own.
consumes_inputs: none. From the definition of familyCost.
statement: (familyCost_nonneg) the family cost is at least 0. (familyCost_mono) if S is contained in T and T
 is feasible, the cost of S is at most the cost of T.
-/
import Definitions.Def_APFPaper1_FamilyCost
import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option autoImplicit false
namespace APFPaper1.Source

theorem familyCost_nonneg {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D) :
    0 ≤ familyCost wholeResource calibration maintained sufficient usesToRealize S := by
  unfold familyCost
  apply Real.sInf_nonneg
  rintro c ⟨p, _, rfl⟩
  exact NNReal.coe_nonneg _

theorem familyCost_mono {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) {S T : Finset D} (hST : S ⊆ T)
    (hT : familyFeasible maintained sufficient usesToRealize T) :
    familyCost wholeResource calibration maintained sufficient usesToRealize S ≤
      familyCost wholeResource calibration maintained sufficient usesToRealize T := by
  obtain ⟨p, hp⟩ := hT
  unfold familyCost
  apply csInf_le_csInf
  · refine ⟨0, fun c hc => ?_⟩
    obtain ⟨q, _, rfl⟩ := hc
    exact NNReal.coe_nonneg _
  · exact ⟨_, p, hp, rfl⟩
  · rintro c ⟨q, hq, rfl⟩
    exact ⟨q, fun d hd => hq d (hST hd), rfl⟩

end APFPaper1.Source


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4
theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {R : Type apfNative_u_3} {Record : Type apfNative_u_4}
  (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set.{apfNative_u_4} Record)
  (sufficient : P → Set.{apfNative_u_4} Record → D → Prop) (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop)
  (S : Finset.{apfNative_u_1} D),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (@APFPaper1.Source.familyCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
      wholeResource calibration maintained sufficient usesToRealize S) := by
  exact @APFPaper1.Source.familyCost_nonneg
