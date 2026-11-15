-- Prove2me | solution 1 for APFPaper5.K1.recordModel_economy
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:14:36.291203+00:00
-- url     : https://prove2.me/submissions/9ccaed7b-bf03-4018-99c0-fa4b458aab7e

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K1_record_model_economy
title: In the record model, a distinction that needs a record of its own is not carried at the cost minimum when a family without it is available
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the adopted RECORDS clause (each distinction has its own records, each record its own cost, the bill
 is the sum; record-book side); Def_APFPaper5_K1_RecordModel. FOUNDATION_INPUTS B07a, A2, in written-out
 form only (see Thm_APFB05_A2_economy for the scope note).
consumes_inputs: none. CONDITIONAL INSTANCE in the supplied record model. A2 appears only as the written-out
 hypothesis hA2 on a supplied set of families; this does not certify a consumption of A2.
statement: (recordModel_extra_record_costs) if a distinction needs a record that the family S does not hold,
 and every record costs at least eps, adding it raises the family cost by at least eps.
 (recordModel_economy) so if the actual family is at the cost minimum of a set of families containing S, and
 eps is positive, the actual family is not S with that distinction added.
not_claimed: that a third direction of a held relation, a second sheet, or a record that sees the common turn
 needs a record of its own; that the smaller family is admissible; the physical statement of A2.
-/
import Definitions.Def_APFPaper5_K1_RecordModel
import Theorems.Thm_APFPaper5_K1_familyCost_weighted
import Theorems.Thm_APFPaper5_K1_recordModelCost_eq
import Theorems.Thm_APFPaper5_K1_recordModel_sharedCost
import Theorems.Thm_APFPaper5_K1_recordModel_satisfies_K1
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K1

universe u v
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec] [DecidableEq ι]

theorem recordModel_extra_record_costs (w : Rec → NNReal) (fam : ι → Finset Rec) (eps : ℝ)
    (hw : ∀ a, eps ≤ (w a : ℝ)) (S : Finset ι) (d : ι) (hneeds : ¬ fam d ⊆ S.biUnion fam) :
    eps ≤ recordModelCost w fam (insert d S) - recordModelCost w fam S := by
  obtain ⟨a, had, haU⟩ := Finset.not_subset.mp hneeds
  rw [recordModelCost_eq, recordModelCost_eq, Finset.biUnion_insert]
  have hsub : insert a (S.biUnion fam) ⊆ fam d ∪ S.biUnion fam := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hxa | hxU
    · rw [hxa]
      exact Finset.mem_union_left _ had
    · exact Finset.mem_union_right _ hxU
  have hsum : ∑ x ∈ insert a (S.biUnion fam), (w x : ℝ) ≤
      ∑ x ∈ fam d ∪ S.biUnion fam, (w x : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => NNReal.coe_nonneg _)
  rw [Finset.sum_insert haU] at hsum
  have hwa := hw a
  linarith

theorem recordModel_economy (w : Rec → NNReal) (fam : ι → Finset Rec) (eps : ℝ) (heps : 0 < eps)
    (hw : ∀ a, eps ≤ (w a : ℝ)) (families : Set (Finset ι)) (actual : Finset ι)
    (hA2 : actual ∈ families ∧
      ∀ a ∈ families, recordModelCost w fam actual ≤ recordModelCost w fam a)
    (S : Finset ι) (d : ι) (hSmem : S ∈ families) (hneeds : ¬ fam d ⊆ S.biUnion fam) :
    actual ≠ insert d S := by
  intro hact
  have hgap := recordModel_extra_record_costs w fam eps hw S d hneeds
  have hle := hA2.2 S hSmem
  rw [hact] at hle
  linarith

end APFPaper5.K1


universe apfNative_u apfNative_v
theorem solution :
∀ {ι : Type apfNative_u} {Rec : Type apfNative_v} [inst : DecidableEq.{apfNative_v + 1} Rec]
  [inst_1 : DecidableEq.{apfNative_u + 1} ι] (w : Rec → NNReal) (fam : ι → Finset.{apfNative_v} Rec) (eps : Real)
  (heps : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps)
  (hw : ∀ (a : Rec), @LE.le.{0} Real Real.instLE eps (NNReal.toReal (w a)))
  (families : Set.{apfNative_u} (Finset.{apfNative_u} ι)) (actual : Finset.{apfNative_u} ι)
  (hA2 :
    And
      (@Membership.mem.{apfNative_u, apfNative_u} (Finset.{apfNative_u} ι) (Set.{apfNative_u} (Finset.{apfNative_u} ι))
        (@Set.instMembership.{apfNative_u} (Finset.{apfNative_u} ι)) families actual)
      (∀ (a : Finset.{apfNative_u} ι),
        @Membership.mem.{apfNative_u, apfNative_u} (Finset.{apfNative_u} ι) (Set.{apfNative_u} (Finset.{apfNative_u} ι))
            (@Set.instMembership.{apfNative_u} (Finset.{apfNative_u} ι)) families a →
          @LE.le.{0} Real Real.instLE (@APFPaper5.K1.recordModelCost.{apfNative_u, apfNative_v} ι Rec w fam actual)
            (@APFPaper5.K1.recordModelCost.{apfNative_u, apfNative_v} ι Rec w fam a)))
  (S : Finset.{apfNative_u} ι) (d : ι)
  (hSmem :
    @Membership.mem.{apfNative_u, apfNative_u} (Finset.{apfNative_u} ι) (Set.{apfNative_u} (Finset.{apfNative_u} ι))
      (@Set.instMembership.{apfNative_u} (Finset.{apfNative_u} ι)) families S)
  (hneeds :
    Not
      (@LE.le.{apfNative_v} (Finset.{apfNative_v} Rec)
        (@Preorder.toLE.{apfNative_v} (Finset.{apfNative_v} Rec)
          (@PartialOrder.toPreorder.{apfNative_v} (Finset.{apfNative_v} Rec)
            (@Finset.instPartialOrder.{apfNative_v} Rec)))
        (fam d) (@Finset.biUnion.{apfNative_u, apfNative_v} ι Rec inst S fam))),
  @Ne.{apfNative_u + 1} (Finset.{apfNative_u} ι) actual
    (@Insert.insert.{apfNative_u, apfNative_u} ι (Finset.{apfNative_u} ι) (@Finset.instInsert.{apfNative_u} ι inst_1) d
      S) := by
  exact @APFPaper5.K1.recordModel_economy
