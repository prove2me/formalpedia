-- Prove2me | solution 1 for APFPaper5.K1.needs_own_record_of_separates
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:20:05.927296+00:00
-- url     : https://prove2.me/submissions/267d3eb3-2883-4510-ae36-80c42c384f84

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K1_record_model_bridge
title: In the record model, a distinction that separates two states the held records do not separate needs a record of its own, is support-novel, and is not carried at the cost minimum
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the adopted RECORDS clause; Def_APFPaper5_K1_RecordModel; Paper 1 Supplement v9.28:2624 (support
 novelty: "every near-optimal protocol for S genuinely lacks a record for d").
consumes_inputs: none. CONDITIONAL INSTANCE in the supplied record model, and CONDITIONAL on hsound: the
 records a distinction needs fix its verdict. A2 appears only written out on a supplied set of families.
statement: (needs_own_record_of_separates) if the records d needs fix its verdict, and two states agree on
 every record held for S but differ in the verdict of d, then d needs a record that S does not hold.
 (recordModel_supportNovel_of_needs_own_record) if every record costs at least a positive eps, a distinction
 that needs a record S does not hold is support-novel over S in the sense of Paper 1.
 (recordModel_economy_of_separation) under the same conditions, if the actual family is at the cost minimum
 of a set of families containing S, it is not S with d added.
not_claimed: hsound for any given distinction; that the family without d is available; the physical
 statement of A2.
-/
import Definitions.Def_APFPaper5_K1_RecordModel
import Theorems.Thm_APFPaper5_K1_familyCost_weighted
import Theorems.Thm_APFPaper5_K1_recordModelCost_eq
import Theorems.Thm_APFPaper5_K1_recordModel_sharedCost
import Theorems.Thm_APFPaper5_K1_recordModel_satisfies_K1
import Theorems.Thm_APFPaper5_K1_recordModel_economy
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source
namespace APFPaper5.K1

universe u v
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec] [DecidableEq ι]

omit [DecidableEq ι] in
theorem needs_own_record_of_separates {Ω Val : Type*} (fam : ι → Finset Rec)
    (reads : Rec → Ω → Val) (verdict : ι → Ω → Prop) (S : Finset ι) (d : ι)
    (hsound : ∀ x y : Ω, (∀ r ∈ fam d, reads r x = reads r y) → (verdict d x ↔ verdict d y))
    (x y : Ω) (hagree : ∀ r ∈ S.biUnion fam, reads r x = reads r y)
    (hne : ¬ (verdict d x ↔ verdict d y)) : ¬ fam d ⊆ S.biUnion fam :=
  fun hsub => hne (hsound x y (fun r hr => hagree r (hsub hr)))

omit [DecidableEq ι] in
theorem recordModel_supportNovel_of_needs_own_record (w : Rec → NNReal) (fam : ι → Finset Rec)
    (eps : ℝ) (heps : 0 < eps) (hw : ∀ a, eps ≤ (w a : ℝ)) (S : Finset ι) (d : ι)
    (hneeds : ¬ fam d ⊆ S.biUnion fam) :
    supportNovel (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
      (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Rec))
      (fun _ sigma e => (↑(fam e) : Set Rec) ⊆ sigma) (fun _ _ _ => True) S d := by
  refine ⟨eps / 2, by linarith, fun p hserve hbill ⟨sigma, hsub, hsuf⟩ => ?_⟩
  obtain ⟨a, had, haU⟩ := Finset.not_subset.mp hneeds
  have hdp : fam d ⊆ p := Finset.coe_subset.mp (hsuf.trans hsub)
  have hSp : S.biUnion fam ⊆ p := by
    intro r hr
    obtain ⟨e, he, hre⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨sg, hsg, hsuf', _⟩ := hserve e he
    exact Finset.mem_coe.mp (hsg (hsuf' (Finset.mem_coe.mpr hre)))
  have hins : insert a (S.biUnion fam) ⊆ p := Finset.insert_subset (hdp had) hSp
  have hsum : ∑ x ∈ insert a (S.biUnion fam), (w x : ℝ) ≤ ∑ x ∈ p, (w x : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hins (fun x _ _ => NNReal.coe_nonneg _)
  rw [Finset.sum_insert haU] at hsum
  have hb : ((∑ x ∈ p, w x : NNReal) : ℝ) ≤
      familyCost (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
        (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Rec))
        (fun _ sigma e => (↑(fam e) : Set Rec) ⊆ sigma) (fun _ _ _ => True) S + eps / 2 := hbill
  rw [NNReal.coe_sum, familyCost_weighted w fam S] at hb
  have hwa := hw a
  linarith

theorem recordModel_economy_of_separation {Ω Val : Type*} (w : Rec → NNReal)
    (fam : ι → Finset Rec) (eps : ℝ) (heps : 0 < eps) (hw : ∀ a, eps ≤ (w a : ℝ))
    (reads : Rec → Ω → Val) (verdict : ι → Ω → Prop) (families : Set (Finset ι))
    (actual : Finset ι)
    (hA2 : actual ∈ families ∧
      ∀ a ∈ families, recordModelCost w fam actual ≤ recordModelCost w fam a)
    (S : Finset ι) (d : ι) (hSmem : S ∈ families)
    (hsound : ∀ x y : Ω, (∀ r ∈ fam d, reads r x = reads r y) → (verdict d x ↔ verdict d y))
    (x y : Ω) (hagree : ∀ r ∈ S.biUnion fam, reads r x = reads r y)
    (hne : ¬ (verdict d x ↔ verdict d y)) : actual ≠ insert d S :=
  recordModel_economy w fam eps heps hw families actual hA2 S d hSmem
    (needs_own_record_of_separates fam reads verdict S d hsound x y hagree hne)

end APFPaper5.K1


universe apfNative_u apfNative_v apfNative_u_1 apfNative_u_2
theorem solution :
∀ {ι : Type apfNative_u} {Rec : Type apfNative_v} [inst : DecidableEq.{apfNative_v + 1} Rec] {Ω : Type apfNative_u_1}
  {Val : Type apfNative_u_2} (fam : ι → Finset.{apfNative_v} Rec) (reads : Rec → Ω → Val) (verdict : ι → Ω → Prop)
  (S : Finset.{apfNative_u} ι) (d : ι)
  (hsound :
    ∀ (x y : Ω),
      (∀ (r : Rec),
          @Membership.mem.{apfNative_v, apfNative_v} Rec (Finset.{apfNative_v} Rec)
              (@SetLike.instMembership.{apfNative_v, apfNative_v} (Finset.{apfNative_v} Rec) Rec
                (@Finset.instSetLike.{apfNative_v} Rec))
              (fam d) r →
            @Eq.{apfNative_u_2 + 1} Val (reads r x) (reads r y)) →
        Iff (verdict d x) (verdict d y))
  (x y : Ω)
  (hagree :
    ∀ (r : Rec),
      @Membership.mem.{apfNative_v, apfNative_v} Rec (Finset.{apfNative_v} Rec)
          (@SetLike.instMembership.{apfNative_v, apfNative_v} (Finset.{apfNative_v} Rec) Rec
            (@Finset.instSetLike.{apfNative_v} Rec))
          (@Finset.biUnion.{apfNative_u, apfNative_v} ι Rec inst S fam) r →
        @Eq.{apfNative_u_2 + 1} Val (reads r x) (reads r y))
  (hne : Not (Iff (verdict d x) (verdict d y))),
  Not
    (@LE.le.{apfNative_v} (Finset.{apfNative_v} Rec)
      (@Preorder.toLE.{apfNative_v} (Finset.{apfNative_v} Rec)
        (@PartialOrder.toPreorder.{apfNative_v} (Finset.{apfNative_v} Rec)
          (@Finset.instPartialOrder.{apfNative_v} Rec)))
      (fam d) (@Finset.biUnion.{apfNative_u, apfNative_v} ι Rec inst S fam)) := by
  exact @APFPaper5.K1.needs_own_record_of_separates
