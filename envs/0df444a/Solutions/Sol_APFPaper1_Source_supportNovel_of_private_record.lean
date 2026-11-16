-- Prove2me | solution 1 for APFPaper1.Source.supportNovel_of_private_record
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:30:51.454313+00:00
-- url     : https://prove2.me/submissions/62999ed0-c2af-4aa5-bb4b-ae4d6134cdc3

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_supportNovel_of_private_record
title: On source data where a bill is the sum of the costs of the records kept, a distinction that needs a record of positive cost which a family does not need is support-novel over that family; one that needs no such record is not, and adds nothing to the cost
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1824 (support novelty: "requires a maintained record that no near-optimal
 admissible joint protocol for S already carries"; "add a derived discriminator reading a digit of an
 already-maintained record ... and the increment vanishes"; a least protocol "need not exist"), 2617-2618
 (independent counting only after support independence is verified), 2624 (Definition, record support),
 2660 and 2753 (no bound for additions that are not support-novel), 3612 (Example, shared coarse record:
 two binary discriminators, one maintained record).
 Def_APFPaper1_FamilyCost (familyCost, supportNovel). Thm_APFPaper1_familyCost_count (this seat, pass 8):
 the count form. Thm_APFPaper5_K1_record_model_bridge (seat 01WrrBvu),
 recordModel_supportNovel_of_needs_own_record: the same implication in the one model where every finite set
 of records is a protocol; here it is proved on any source data meeting the named sentences.
 The author, 2026-11-14 16:45 HST, "Proceed as advised" (RULING_named_calls_2026-11-14): own records (hneed)
 taken as a reading of RECORDS; availability and the bill as a sum as read on 2026-11-14 13:00 HST.
 Codebank: apf/kappa_int_bounds.py names support-novel increments; nothing there on private records.
consumes_inputs: none. Ordinary mathematics on the source data of the family-cost definition.
named_hypotheses: hbill (a protocol's bill is the sum of the costs of the records it keeps), hkept (what it
 maintains is what it keeps), hneed (OWN RECORDS: a set of records sufficient for d contains the records d
 needs), havail (AVAILABILITY at the family in hand: some admitted protocol keeps exactly the records the
 family needs, and serves it). In the last two theorems only, hsuff (having the records d needs is enough to
 serve d). hsuff is NOT an adopted reading; it is the converse of hneed and is named.
statement: (sum_needed_le_bill) a protocol serving S bills at least the cost of the records S needs.
 (familyCost_eq_sum_of_available) with availability at S, the cost of S is the cost of the records S needs.
 (supportNovel_of_private_record) with availability at S, if d needs a record of positive cost that S does
 not need, d is support-novel over S. (supportNovel_of_private_record_count) the same where every record
 costs one unit. (marginal_ge_of_private_record) and adding d raises the cost by at least the cost of that
 record. (each_private_excludes_riding, supportNovel_of_each_private) if EVERY distinction has a record no
 other distinction needs, every distinction is support-novel over every family it is not in.
 (marginal_zero_of_no_own_record) if S already needs every record d needs, adding d adds nothing to the
 cost. (needs_own_record_of_supportNovel) under hsuff, a distinction support-novel over S needs a record S
 does not need.
not_claimed: that every distinction has a private record. Said of every distinction, that sentence excludes
 the Supplement's shared-coarse-record example (3612), in which neither discriminator has a record the
 other does not need; by marginal_zero_of_no_own_record each adds nothing over the other, as 1824 and 2753
 say. The theorems here take the private record as a hypothesis on the family in hand. Availability is not
 derived (Thm_APFB06_count_worlds), and the Supplement does not grant a least protocol in general. hsuff.
-/
import Theorems.Thm_APFPaper1_Source_needed_subset_kept
import Theorems.Thm_APFPaper1_Source_card_needed_le_bill
import Theorems.Thm_APFPaper1_Source_card_needed_le_familyCost
import Theorems.Thm_APFPaper1_Source_familyCost_eq_card_of_available
import Theorems.Thm_APFPaper1_Source_join_of_available
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace APFPaper1.Source

section
variable {D P R Record : Type*} [DecidableEq Record]
  (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)
  (kept : P → Finset Record) (fam : D → Finset Record) (cost : Record → NNReal)

/-- A protocol that serves S bills at least the cost of the records S needs. -/
theorem sum_needed_le_bill
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D) (p : P)
    (hp : ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) :
    ∑ r ∈ S.biUnion fam, (cost r : ℝ) ≤ (calibration (wholeResource p) : ℝ) := by
  rw [hbill p]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (needed_subset_kept maintained sufficient usesToRealize kept fam hkept hneed S p hp)
    (fun x _ _ => NNReal.coe_nonneg _)

/-- With availability at S, the cost of S is the cost of the records S needs. -/
theorem familyCost_eq_sum_of_available
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D)
    (havail : ∃ p : P, kept p = S.biUnion fam ∧ ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) :
    familyCost wholeResource calibration maintained sufficient usesToRealize S =
      ∑ r ∈ S.biUnion fam, (cost r : ℝ) := by
  obtain ⟨p, hk, hp⟩ := havail
  apply le_antisymm
  · have h : familyCost wholeResource calibration maintained sufficient usesToRealize S ≤
        (calibration (wholeResource p) : ℝ) :=
      csInf_le ⟨0, by rintro c ⟨q, _, rfl⟩; exact NNReal.coe_nonneg _⟩ ⟨p, hp, rfl⟩
    rw [hbill p, hk] at h
    exact h
  · refine le_csInf ⟨_, p, hp, rfl⟩ ?_
    rintro c ⟨q, hq, rfl⟩
    exact sum_needed_le_bill wholeResource calibration maintained sufficient usesToRealize kept fam
      cost hbill hkept hneed S q hq

/-- A distinction that needs a record of positive cost which S does not need is support-novel
over S. -/
theorem supportNovel_of_private_record
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D) (d : D)
    (havail : ∃ p : P, kept p = S.biUnion fam ∧ ∀ e ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma e ∧ usesToRealize p e sigma)
    (a : Record) (had : a ∈ fam d) (haS : a ∉ S.biUnion fam) (hpos : 0 < cost a) :
    supportNovel wholeResource calibration maintained sufficient usesToRealize S d := by
  have hposR : (0 : ℝ) < (cost a : ℝ) := NNReal.coe_pos.mpr hpos
  refine ⟨(cost a : ℝ) / 2, by linarith, fun p hserve hb ⟨sigma, hsub, hsuf⟩ => ?_⟩
  have hSp : S.biUnion fam ⊆ kept p :=
    needed_subset_kept maintained sufficient usesToRealize kept fam hkept hneed S p hserve
  have hap : a ∈ kept p := by
    have h : a ∈ maintained p := hsub (hneed p sigma d hsuf (Finset.mem_coe.mpr had))
    rw [hkept p] at h
    exact Finset.mem_coe.mp h
  have hins : insert a (S.biUnion fam) ⊆ kept p := Finset.insert_subset hap hSp
  have hsum : ∑ x ∈ insert a (S.biUnion fam), (cost x : ℝ) ≤ ∑ x ∈ kept p, (cost x : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hins (fun x _ _ => NNReal.coe_nonneg _)
  rw [Finset.sum_insert haS] at hsum
  rw [familyCost_eq_sum_of_available wholeResource calibration maintained sufficient usesToRealize
    kept fam cost hbill hkept hneed S havail, hbill p] at hb
  linarith

/-- The same where every record costs one unit: the count form of
`Thm_APFPaper1_familyCost_count`. -/
theorem supportNovel_of_private_record_count
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ((kept p).card : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D) (d : D)
    (havail : ∃ p : P, kept p = S.biUnion fam ∧ ∀ e ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma e ∧ usesToRealize p e sigma)
    (hpriv : ¬ fam d ⊆ S.biUnion fam) :
    supportNovel wholeResource calibration maintained sufficient usesToRealize S d := by
  obtain ⟨a, had, haS⟩ := Finset.not_subset.mp hpriv
  refine supportNovel_of_private_record wholeResource calibration maintained sufficient
    usesToRealize kept fam (fun _ => (1 : NNReal)) ?_ hkept hneed S d havail a had haS one_pos
  intro p
  rw [hbill p]
  simp

/-- Adding a distinction that needs a record S does not need raises the cost by at least the cost
of that record. -/
theorem marginal_ge_of_private_record [DecidableEq D]
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D) (d : D)
    (havail : ∃ p : P, kept p = S.biUnion fam ∧ ∀ e ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma e ∧ usesToRealize p e sigma)
    (havail' : ∃ p : P, kept p = (insert d S).biUnion fam ∧ ∀ e ∈ insert d S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma e ∧ usesToRealize p e sigma)
    (a : Record) (had : a ∈ fam d) (haS : a ∉ S.biUnion fam) :
    familyCost wholeResource calibration maintained sufficient usesToRealize S + (cost a : ℝ) ≤
      familyCost wholeResource calibration maintained sufficient usesToRealize (insert d S) := by
  rw [familyCost_eq_sum_of_available wholeResource calibration maintained sufficient usesToRealize
      kept fam cost hbill hkept hneed S havail,
    familyCost_eq_sum_of_available wholeResource calibration maintained sufficient usesToRealize
      kept fam cost hbill hkept hneed (insert d S) havail']
  have hins : insert a (S.biUnion fam) ⊆ (insert d S).biUnion fam := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr'
    · exact Finset.mem_biUnion.mpr ⟨d, Finset.mem_insert_self _ _, had⟩
    · obtain ⟨e, he, hre⟩ := Finset.mem_biUnion.mp hr'
      exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_insert_of_mem he, hre⟩
  have hsum : ∑ x ∈ insert a (S.biUnion fam), (cost x : ℝ) ≤
      ∑ x ∈ (insert d S).biUnion fam, (cost x : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hins (fun x _ _ => NNReal.coe_nonneg _)
  rw [Finset.sum_insert haS] at hsum
  linarith

/-- If every distinction has a record no other distinction needs, no distinction outside a family
has all its records among those the family needs. -/
theorem each_private_excludes_riding
    (hprivate : ∀ d : D, ∃ a ∈ fam d, ∀ e : D, e ≠ d → a ∉ fam e)
    (S : Finset D) (d : D) (hd : d ∉ S) : ¬ fam d ⊆ S.biUnion fam := by
  intro hsub
  obtain ⟨a, had, hae⟩ := hprivate d
  obtain ⟨e, he, hre⟩ := Finset.mem_biUnion.mp (hsub had)
  exact hae e (fun h => hd (h ▸ he)) hre

/-- If every distinction has a record of positive cost that no other distinction needs, every
distinction is support-novel over every family it is not in. -/
theorem supportNovel_of_each_private
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (havail : ∀ S : Finset D, ∃ p : P, kept p = S.biUnion fam ∧ ∀ e ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma e ∧ usesToRealize p e sigma)
    (hprivate : ∀ d : D, ∃ a ∈ fam d, 0 < cost a ∧ ∀ e : D, e ≠ d → a ∉ fam e)
    (S : Finset D) (d : D) (hd : d ∉ S) :
    supportNovel wholeResource calibration maintained sufficient usesToRealize S d := by
  obtain ⟨a, had, hpos, hae⟩ := hprivate d
  refine supportNovel_of_private_record wholeResource calibration maintained sufficient
    usesToRealize kept fam cost hbill hkept hneed S d (havail S) a had ?_ hpos
  intro hmem
  obtain ⟨e, he, hre⟩ := Finset.mem_biUnion.mp hmem
  exact hae e (fun h => hd (h ▸ he)) hre

/-- If S already needs every record d needs, adding d adds nothing to the cost: the Supplement's
derived discriminator (1824, 2753, 3612). -/
theorem marginal_zero_of_no_own_record [DecidableEq D]
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D) (d : D)
    (havail : ∃ p : P, kept p = S.biUnion fam ∧ ∀ e ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma e ∧ usesToRealize p e sigma)
    (havail' : ∃ p : P, kept p = (insert d S).biUnion fam ∧ ∀ e ∈ insert d S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma e ∧ usesToRealize p e sigma)
    (hsub : fam d ⊆ S.biUnion fam) :
    familyCost wholeResource calibration maintained sufficient usesToRealize (insert d S) =
      familyCost wholeResource calibration maintained sufficient usesToRealize S := by
  rw [familyCost_eq_sum_of_available wholeResource calibration maintained sufficient usesToRealize
      kept fam cost hbill hkept hneed S havail,
    familyCost_eq_sum_of_available wholeResource calibration maintained sufficient usesToRealize
      kept fam cost hbill hkept hneed (insert d S) havail']
  have heq : (insert d S).biUnion fam = S.biUnion fam := by
    rw [Finset.biUnion_insert]
    exact Finset.union_eq_right.mpr hsub
  rw [heq]

/-- Under hsuff (having the records d needs is enough to serve d; not an adopted reading), a
distinction that is support-novel over S needs a record S does not need. -/
theorem needs_own_record_of_supportNovel
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (hsuff : ∀ (p : P) (sigma : Set Record) (d : D),
      (↑(fam d) : Set Record) ⊆ sigma → sufficient p sigma d)
    (S : Finset D) (d : D)
    (havail : ∃ p : P, kept p = S.biUnion fam ∧ ∀ e ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma e ∧ usesToRealize p e sigma)
    (hnov : supportNovel wholeResource calibration maintained sufficient usesToRealize S d) :
    ¬ fam d ⊆ S.biUnion fam := by
  intro hsub
  obtain ⟨eta, heta, h⟩ := hnov
  have hc := familyCost_eq_sum_of_available wholeResource calibration maintained sufficient
    usesToRealize kept fam cost hbill hkept hneed S havail
  obtain ⟨p, hk, hp⟩ := havail
  refine h p hp ?_ ⟨maintained p, fun _ hr => hr, hsuff p _ d ?_⟩
  · rw [hc, hbill p, hk]
    linarith
  · rw [hkept p, hk]
    exact Finset.coe_subset.mpr hsub

end

end APFPaper1.Source

#print axioms APFPaper1.Source.sum_needed_le_bill
#print axioms APFPaper1.Source.familyCost_eq_sum_of_available
#print axioms APFPaper1.Source.supportNovel_of_private_record
#print axioms APFPaper1.Source.supportNovel_of_private_record_count
#print axioms APFPaper1.Source.marginal_ge_of_private_record
#print axioms APFPaper1.Source.each_private_excludes_riding
#print axioms APFPaper1.Source.supportNovel_of_each_private
#print axioms APFPaper1.Source.marginal_zero_of_no_own_record
#print axioms APFPaper1.Source.needs_own_record_of_supportNovel


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4
theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {R : Type apfNative_u_3} {Record : Type apfNative_u_4}
  [inst : DecidableEq.{apfNative_u_4 + 1} Record] (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set.{apfNative_u_4} Record) (sufficient : P → Set.{apfNative_u_4} Record → D → Prop)
  (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop) (kept : P → Finset.{apfNative_u_4} Record)
  (fam : D → Finset.{apfNative_u_4} Record) (cost : Record → NNReal)
  (hbill :
    ∀ (p : P),
      @Eq.{1} Real (NNReal.toReal (calibration (wholeResource p)))
        (@Finset.sum.{apfNative_u_4, 0} Record Real Real.instAddCommMonoid (kept p) fun (r : Record) =>
          NNReal.toReal (cost r)))
  (hkept :
    ∀ (p : P),
      @Eq.{apfNative_u_4 + 1} (Set.{apfNative_u_4} Record) (maintained p)
        (@SetLike.coe.{apfNative_u_4, apfNative_u_4} (Finset.{apfNative_u_4} Record) Record
          (@Finset.instSetLike.{apfNative_u_4} Record) (kept p)))
  (hneed :
    ∀ (p : P) (sigma : Set.{apfNative_u_4} Record) (d : D),
      sufficient p sigma d →
        @LE.le.{apfNative_u_4} (Set.{apfNative_u_4} Record) (@Set.instLE.{apfNative_u_4} Record)
          (@SetLike.coe.{apfNative_u_4, apfNative_u_4} (Finset.{apfNative_u_4} Record) Record
            (@Finset.instSetLike.{apfNative_u_4} Record) (fam d))
          sigma)
  (S : Finset.{apfNative_u_1} D) (d : D)
  (havail :
    @Exists.{apfNative_u_2 + 1} P fun (p : P) =>
      And
        (@Eq.{apfNative_u_4 + 1} (Finset.{apfNative_u_4} Record) (kept p)
          (@Finset.biUnion.{apfNative_u_1, apfNative_u_4} D Record inst S fam))
        (∀ (e : D),
          @Membership.mem.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
              (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1} (Finset.{apfNative_u_1} D) D
                (@Finset.instSetLike.{apfNative_u_1} D))
              S e →
            @Exists.{apfNative_u_4 + 1} (Set.{apfNative_u_4} Record) fun (sigma : Set.{apfNative_u_4} Record) =>
              And
                (@LE.le.{apfNative_u_4} (Set.{apfNative_u_4} Record) (@Set.instLE.{apfNative_u_4} Record) sigma
                  (maintained p))
                (And (sufficient p sigma e) (usesToRealize p e sigma))))
  (a : Record)
  (had :
    @Membership.mem.{apfNative_u_4, apfNative_u_4} Record (Finset.{apfNative_u_4} Record)
      (@SetLike.instMembership.{apfNative_u_4, apfNative_u_4} (Finset.{apfNative_u_4} Record) Record
        (@Finset.instSetLike.{apfNative_u_4} Record))
      (fam d) a)
  (haS :
    Not
      (@Membership.mem.{apfNative_u_4, apfNative_u_4} Record (Finset.{apfNative_u_4} Record)
        (@SetLike.instMembership.{apfNative_u_4, apfNative_u_4} (Finset.{apfNative_u_4} Record) Record
          (@Finset.instSetLike.{apfNative_u_4} Record))
        (@Finset.biUnion.{apfNative_u_1, apfNative_u_4} D Record inst S fam) a))
  (hpos :
    @LT.lt.{0} NNReal (@Preorder.toLT.{0} NNReal (@PartialOrder.toPreorder.{0} NNReal NNReal.instPartialOrder))
      (@OfNat.ofNat.{0} NNReal (nat_lit 0) (@Zero.toOfNat0.{0} NNReal NNReal.instZero)) (cost a)),
  @APFPaper1.Source.supportNovel.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record wholeResource
    calibration maintained sufficient usesToRealize S d := by
  exact @APFPaper1.Source.supportNovel_of_private_record
