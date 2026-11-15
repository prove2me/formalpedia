-- Prove2me | solution 1 for APFPaper1.Source.familyCost_eq_card_of_available
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T18:42:56.925882+00:00
-- url     : https://prove2.me/submissions/7989efe6-0ee5-4d90-84ee-8ccf14ea31c7

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_familyCost_count
title: Family cost is at least the number of records the family needs, and equals it when some admitted protocol keeps exactly those records
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFPaper1_FamilyCost (Paper 1 Supplement v9.28:1786-1790, the ledger valuation convention).
 Supplement v9.28:2426-2470 (additivity under factorized support), 2502-2530 (support-local additive
 accounting). Thm_APFPaper5_K1_shared_cost_counting (seat 01WrrBvu): familyCost_counting, the same equality
 in the model where every finite set of records is a protocol. RULING_records_clause_2026-11-12 and
 RULING_bill_is_a_sum_2026-11-13 (a bill is a sum over the records kept). Codebank apf/delta_calculus.py
 (cost as the floor times a count of channels, clause L_cost).
consumes_inputs: none. A statement about the source data of the family-cost definition.
named_hypotheses: hbill (a protocol's bill is the number of records it keeps), hkept (what it maintains is
 what it keeps), hneed (a set of records sufficient for d contains the records d needs), havail, the
 AVAILABILITY CLAUSE (some admitted protocol keeps exactly the records the family needs, and serves it).
statement: (card_needed_le_bill) under hbill, hkept and hneed, a protocol serving S bills at least the
 number of records S needs. (card_needed_le_familyCost) so a feasible S costs at least that number.
 (familyCost_eq_card_of_available) with the availability clause at S, the cost of S is that number.
 (join_of_available) with the availability clause at S ∪ T, any protocol serving S and any serving T are
 matched by one serving S ∪ T for at most the two bills together: the join clause of
 Thm_APFPaper1_familyCost_subadditive_of_join.
not_claimed: the availability clause. It does not follow from the eight declared forms, the two readings
 of 2026-11-13, or from bills being counts: see Thm_APFB06_count_worlds. Weighted records are not treated;
 every record here costs one unit.
-/
import Definitions.Def_APFPaper1_FamilyCost
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace APFPaper1.Source

section
variable {D P R Record : Type*} [DecidableEq Record]
  (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)
  (kept : P → Finset Record) (fam : D → Finset Record)

/-- A protocol that serves S keeps every record S needs. -/
theorem needed_subset_kept
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D) (p : P)
    (hp : ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) :
    S.biUnion fam ⊆ kept p := by
  intro r hr
  obtain ⟨d, hd, hrd⟩ := Finset.mem_biUnion.mp hr
  obtain ⟨sigma, hsig, hsuf, _⟩ := hp d hd
  have h : r ∈ maintained p := hsig (hneed p sigma d hsuf (Finset.mem_coe.mpr hrd))
  rw [hkept p] at h
  exact Finset.mem_coe.mp h

theorem card_needed_le_bill
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ((kept p).card : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D) (p : P)
    (hp : ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) :
    ((S.biUnion fam).card : ℝ) ≤ (calibration (wholeResource p) : ℝ) := by
  rw [hbill p]
  exact_mod_cast Finset.card_le_card
    (needed_subset_kept maintained sufficient usesToRealize kept fam hkept hneed S p hp)

theorem card_needed_le_familyCost
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ((kept p).card : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D)
    (hS : familyFeasible maintained sufficient usesToRealize S) :
    ((S.biUnion fam).card : ℝ) ≤
      familyCost wholeResource calibration maintained sufficient usesToRealize S := by
  obtain ⟨p0, hp0⟩ := hS
  refine le_csInf ⟨_, p0, hp0, rfl⟩ ?_
  rintro c ⟨p, hp, rfl⟩
  exact card_needed_le_bill wholeResource calibration maintained sufficient usesToRealize kept fam
    hbill hkept hneed S p hp

theorem familyCost_eq_card_of_available
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ((kept p).card : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D)
    (havail : ∃ p : P, kept p = S.biUnion fam ∧ ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) :
    familyCost wholeResource calibration maintained sufficient usesToRealize S =
      ((S.biUnion fam).card : ℝ) := by
  obtain ⟨p, hk, hp⟩ := havail
  apply le_antisymm
  · have h : familyCost wholeResource calibration maintained sufficient usesToRealize S ≤
        (calibration (wholeResource p) : ℝ) :=
      csInf_le ⟨0, by rintro c ⟨q, _, rfl⟩; exact NNReal.coe_nonneg _⟩ ⟨p, hp, rfl⟩
    rw [hbill p, hk] at h
    exact h
  · exact card_needed_le_familyCost wholeResource calibration maintained sufficient usesToRealize
      kept fam hbill hkept hneed S ⟨p, hp⟩

theorem join_of_available [DecidableEq D]
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ((kept p).card : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S T : Finset D)
    (havail : ∃ p : P, kept p = (S ∪ T).biUnion fam ∧ ∀ d ∈ S ∪ T, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma)
    (p q : P)
    (hp : ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma)
    (hq : ∀ d ∈ T, ∃ sigma : Set Record,
      sigma ⊆ maintained q ∧ sufficient q sigma d ∧ usesToRealize q d sigma) :
    ∃ pq : P,
      (∀ d ∈ S ∪ T, ∃ sigma : Set Record,
        sigma ⊆ maintained pq ∧ sufficient pq sigma d ∧ usesToRealize pq d sigma) ∧
      (calibration (wholeResource pq) : ℝ) ≤
        (calibration (wholeResource p) : ℝ) + (calibration (wholeResource q) : ℝ) := by
  obtain ⟨pq, hk, hpq⟩ := havail
  refine ⟨pq, hpq, ?_⟩
  have hsubP := needed_subset_kept maintained sufficient usesToRealize kept fam hkept hneed S p hp
  have hsubQ := needed_subset_kept maintained sufficient usesToRealize kept fam hkept hneed T q hq
  have hsub : (S ∪ T).biUnion fam ⊆ kept p ∪ kept q := by
    intro r hr
    obtain ⟨d, hd, hrd⟩ := Finset.mem_biUnion.mp hr
    rcases Finset.mem_union.mp hd with hdS | hdT
    · exact Finset.mem_union_left _ (hsubP (Finset.mem_biUnion.mpr ⟨d, hdS, hrd⟩))
    · exact Finset.mem_union_right _ (hsubQ (Finset.mem_biUnion.mpr ⟨d, hdT, hrd⟩))
  have hcard : ((S ∪ T).biUnion fam).card ≤ (kept p).card + (kept q).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  rw [hbill pq, hbill p, hbill q, hk]
  exact_mod_cast hcard

end

end APFPaper1.Source


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4
theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {R : Type apfNative_u_3} {Record : Type apfNative_u_4}
  [inst : DecidableEq.{apfNative_u_4 + 1} Record] (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set.{apfNative_u_4} Record) (sufficient : P → Set.{apfNative_u_4} Record → D → Prop)
  (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop) (kept : P → Finset.{apfNative_u_4} Record)
  (fam : D → Finset.{apfNative_u_4} Record)
  (hbill :
    ∀ (p : P),
      @Eq.{1} Real (NNReal.toReal (calibration (wholeResource p)))
        (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{apfNative_u_4} Record (kept p))))
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
  (S : Finset.{apfNative_u_1} D)
  (havail :
    @Exists.{apfNative_u_2 + 1} P fun (p : P) =>
      And
        (@Eq.{apfNative_u_4 + 1} (Finset.{apfNative_u_4} Record) (kept p)
          (@Finset.biUnion.{apfNative_u_1, apfNative_u_4} D Record inst S fam))
        (∀ (d : D),
          @Membership.mem.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
              (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1} (Finset.{apfNative_u_1} D) D
                (@Finset.instSetLike.{apfNative_u_1} D))
              S d →
            @Exists.{apfNative_u_4 + 1} (Set.{apfNative_u_4} Record) fun (sigma : Set.{apfNative_u_4} Record) =>
              And
                (@LE.le.{apfNative_u_4} (Set.{apfNative_u_4} Record) (@Set.instLE.{apfNative_u_4} Record) sigma
                  (maintained p))
                (And (sufficient p sigma d) (usesToRealize p d sigma)))),
  @Eq.{1} Real
    (@APFPaper1.Source.familyCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
      wholeResource calibration maintained sufficient usesToRealize S)
    (@Nat.cast.{0} Real Real.instNatCast
      (@Finset.card.{apfNative_u_4} Record (@Finset.biUnion.{apfNative_u_1, apfNative_u_4} D Record inst S fam))) := by
  exact @APFPaper1.Source.familyCost_eq_card_of_available
