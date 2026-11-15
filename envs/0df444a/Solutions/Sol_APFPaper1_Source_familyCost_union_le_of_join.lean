-- Prove2me | solution 1 for APFPaper1.Source.familyCost_union_le_of_join
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:09:33.096613+00:00
-- url     : https://prove2.me/submissions/1556ad2e-752d-42ee-a11c-ca90e4115b30

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-13; not
 gated, not reviewed, not released, not built on the build box)
name: APFPaper1_familyCost_subadditive_of_join
title: Family cost is subadditive on a pair of families when their protocols can be run side by side for at most the sum of their bills
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFPaper1_FamilyCost (Supplement v9.28:1786-1790, the ledger valuation convention).
 Supplement v9.28:1779-1781 (the residue kappa_int, of either sign), 2426-2470 (additivity is proved there
 only under factorized support), 3066 ("parallel separate protocols"). Def_APFPaper5_K1_SharedCost and
 APFPaper5.K1.sharedCost_nonneg_iff (seat 01WrrBvu, unchanged). Codebank apf/delta_calculus.py, note F2:
 the sign of Delta is not fixed once anchors intersect.
consumes_inputs: none. A statement about the source data of the family-cost definition.
named_hypothesis: hjoin, the JOIN CLAUSE. For a protocol serving S and a protocol serving T there is a
 protocol serving every member of S and of T whose bill is at most the two bills together. In the second
 theorem it is asked only when the two bills together are within capacity.
statement: (familyCost_le_bill) the family cost is at most the bill of any protocol serving the family.
 (exists_serving_near_cost) a feasible family has a serving protocol billing less than its cost plus any
 positive tolerance. (familyCost_union_le_of_join) under the join clause, for feasible S and T, the cost
 of S ∪ T is at most the cost of S plus the cost of T. (familyCost_union_le_of_join_within_capacity) the
 same when the join clause is asked only within capacity C and S ∪ T is ledger-admissible at C.
 (sharedCost_familyCost_nonneg_of_join) so the shared cost of S and T is nonnegative.
not_claimed: the join clause. It does not follow from the eight declared forms or from the readings of
 2026-11-13: see Thm_APFB06_subadditivity_worlds. Nothing about equality (additivity).
-/
import Definitions.Def_APFPaper1_FamilyCost
import Theorems.Thm_APFPaper5_K1_sharedCost_self
import Theorems.Thm_APFPaper5_K1_sharedCost_le_right
import Theorems.Thm_APFPaper5_K1_sharedCost_le_left
import Theorems.Thm_APFPaper5_K1_sharedCost_nonneg_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_ledger
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_no_joint
import Theorems.Thm_APFPaper5_K1_cost_is_count_times_floor
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace APFPaper1.Source

theorem familyCost_le_bill {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D) (p : P)
    (hp : ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) :
    familyCost wholeResource calibration maintained sufficient usesToRealize S ≤
      (calibration (wholeResource p) : ℝ) :=
  csInf_le ⟨0, by rintro c ⟨q, _, rfl⟩; exact NNReal.coe_nonneg _⟩ ⟨p, hp, rfl⟩

theorem exists_serving_near_cost {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D)
    (hS : familyFeasible maintained sufficient usesToRealize S) (e : ℝ) (he : 0 < e) :
    ∃ p : P,
      (∀ d ∈ S, ∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) ∧
      (calibration (wholeResource p) : ℝ) <
        familyCost wholeResource calibration maintained sufficient usesToRealize S + e := by
  obtain ⟨p0, hp0⟩ := hS
  have hne : ({c : ℝ | ∃ p : P,
      (∀ d ∈ S, ∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) ∧
      (calibration (wholeResource p) : ℝ) = c}).Nonempty := ⟨_, p0, hp0, rfl⟩
  obtain ⟨c, ⟨p, hp, rfl⟩, hc⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right _ he)
  exact ⟨p, hp, hc⟩

theorem familyCost_union_le_of_join {D P R Record : Type*} [DecidableEq D]
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S T : Finset D)
    (hS : familyFeasible maintained sufficient usesToRealize S)
    (hT : familyFeasible maintained sufficient usesToRealize T)
    (hjoin : ∀ p q : P,
      (∀ d ∈ S, ∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) →
      (∀ d ∈ T, ∃ sigma : Set Record,
        sigma ⊆ maintained q ∧ sufficient q sigma d ∧ usesToRealize q d sigma) →
      ∃ pq : P,
        (∀ d ∈ S ∪ T, ∃ sigma : Set Record,
          sigma ⊆ maintained pq ∧ sufficient pq sigma d ∧ usesToRealize pq d sigma) ∧
        (calibration (wholeResource pq) : ℝ) ≤
          (calibration (wholeResource p) : ℝ) + (calibration (wholeResource q) : ℝ)) :
    familyCost wholeResource calibration maintained sufficient usesToRealize (S ∪ T) ≤
      familyCost wholeResource calibration maintained sufficient usesToRealize S +
        familyCost wholeResource calibration maintained sufficient usesToRealize T := by
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨p, hp, hpb⟩ := exists_serving_near_cost wholeResource calibration maintained sufficient
    usesToRealize S hS (eps / 2) (by linarith)
  obtain ⟨q, hq, hqb⟩ := exists_serving_near_cost wholeResource calibration maintained sufficient
    usesToRealize T hT (eps / 2) (by linarith)
  obtain ⟨pq, hpq, hbill⟩ := hjoin p q hp hq
  have h := familyCost_le_bill wholeResource calibration maintained sufficient usesToRealize
    (S ∪ T) pq hpq
  linarith

theorem familyCost_union_le_of_join_within_capacity {D P R Record : Type*} [DecidableEq D]
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (C : ℝ) (S T : Finset D)
    (hS : familyFeasible maintained sufficient usesToRealize S)
    (hT : familyFeasible maintained sufficient usesToRealize T)
    (hU : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C (S ∪ T))
    (hjoin : ∀ p q : P,
      (∀ d ∈ S, ∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) →
      (∀ d ∈ T, ∃ sigma : Set Record,
        sigma ⊆ maintained q ∧ sufficient q sigma d ∧ usesToRealize q d sigma) →
      (calibration (wholeResource p) : ℝ) + (calibration (wholeResource q) : ℝ) ≤ C →
      ∃ pq : P,
        (∀ d ∈ S ∪ T, ∃ sigma : Set Record,
          sigma ⊆ maintained pq ∧ sufficient pq sigma d ∧ usesToRealize pq d sigma) ∧
        (calibration (wholeResource pq) : ℝ) ≤
          (calibration (wholeResource p) : ℝ) + (calibration (wholeResource q) : ℝ)) :
    familyCost wholeResource calibration maintained sufficient usesToRealize (S ∪ T) ≤
      familyCost wholeResource calibration maintained sufficient usesToRealize S +
        familyCost wholeResource calibration maintained sufficient usesToRealize T := by
  by_cases hlt : familyCost wholeResource calibration maintained sufficient usesToRealize S +
      familyCost wholeResource calibration maintained sufficient usesToRealize T < C
  · apply le_of_forall_pos_le_add
    intro eps heps
    obtain ⟨delta, hd0, hde, hdC⟩ : ∃ delta : ℝ, 0 < delta ∧ delta ≤ eps ∧
        familyCost wholeResource calibration maintained sufficient usesToRealize S +
          familyCost wholeResource calibration maintained sufficient usesToRealize T + delta ≤ C := by
      refine ⟨min eps (C - (familyCost wholeResource calibration maintained sufficient usesToRealize S +
        familyCost wholeResource calibration maintained sufficient usesToRealize T)),
        lt_min heps (by linarith), min_le_left _ _, ?_⟩
      have h := min_le_right eps
        (C - (familyCost wholeResource calibration maintained sufficient usesToRealize S +
          familyCost wholeResource calibration maintained sufficient usesToRealize T))
      linarith
    obtain ⟨p, hp, hpb⟩ := exists_serving_near_cost wholeResource calibration maintained sufficient
      usesToRealize S hS (delta / 2) (by linarith)
    obtain ⟨q, hq, hqb⟩ := exists_serving_near_cost wholeResource calibration maintained sufficient
      usesToRealize T hT (delta / 2) (by linarith)
    obtain ⟨pq, hpq, hbill⟩ := hjoin p q hp hq (by linarith)
    have h := familyCost_le_bill wholeResource calibration maintained sufficient usesToRealize
      (S ∪ T) pq hpq
    linarith
  · exact le_trans hU.2 (not_lt.mp hlt)

end APFPaper1.Source

open APFPaper1.Source in
theorem APFPaper5.K1.sharedCost_familyCost_nonneg_of_join {D P R Record : Type*} [DecidableEq D]
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (C : ℝ) (S T : Finset D)
    (hS : familyFeasible maintained sufficient usesToRealize S)
    (hT : familyFeasible maintained sufficient usesToRealize T)
    (hU : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C (S ∪ T))
    (hjoin : ∀ p q : P,
      (∀ d ∈ S, ∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) →
      (∀ d ∈ T, ∃ sigma : Set Record,
        sigma ⊆ maintained q ∧ sufficient q sigma d ∧ usesToRealize q d sigma) →
      (calibration (wholeResource p) : ℝ) + (calibration (wholeResource q) : ℝ) ≤ C →
      ∃ pq : P,
        (∀ d ∈ S ∪ T, ∃ sigma : Set Record,
          sigma ⊆ maintained pq ∧ sufficient pq sigma d ∧ usesToRealize pq d sigma) ∧
        (calibration (wholeResource pq) : ℝ) ≤
          (calibration (wholeResource p) : ℝ) + (calibration (wholeResource q) : ℝ)) :
    0 ≤ APFPaper5.K1.sharedCost
      (familyCost wholeResource calibration maintained sufficient usesToRealize) S T :=
  (APFPaper5.K1.sharedCost_nonneg_iff _ S T).mpr
    (familyCost_union_le_of_join_within_capacity wholeResource calibration maintained sufficient
      usesToRealize C S T hS hT hU hjoin)


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4
theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {R : Type apfNative_u_3} {Record : Type apfNative_u_4}
  [inst : DecidableEq.{apfNative_u_1 + 1} D] (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set.{apfNative_u_4} Record) (sufficient : P → Set.{apfNative_u_4} Record → D → Prop)
  (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop) (S T : Finset.{apfNative_u_1} D)
  (hS :
    @APFPaper1.Source.familyFeasible.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
      usesToRealize S)
  (hT :
    @APFPaper1.Source.familyFeasible.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
      usesToRealize T)
  (hjoin :
    ∀ (p q : P),
      (∀ (d : D),
          @Membership.mem.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
              (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1} (Finset.{apfNative_u_1} D) D
                (@Finset.instSetLike.{apfNative_u_1} D))
              S d →
            @Exists.{apfNative_u_4 + 1} (Set.{apfNative_u_4} Record) fun (sigma : Set.{apfNative_u_4} Record) =>
              And
                (@LE.le.{apfNative_u_4} (Set.{apfNative_u_4} Record) (@Set.instLE.{apfNative_u_4} Record) sigma
                  (maintained p))
                (And (sufficient p sigma d) (usesToRealize p d sigma))) →
        (∀ (d : D),
            @Membership.mem.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
                (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1} (Finset.{apfNative_u_1} D) D
                  (@Finset.instSetLike.{apfNative_u_1} D))
                T d →
              @Exists.{apfNative_u_4 + 1} (Set.{apfNative_u_4} Record) fun (sigma : Set.{apfNative_u_4} Record) =>
                And
                  (@LE.le.{apfNative_u_4} (Set.{apfNative_u_4} Record) (@Set.instLE.{apfNative_u_4} Record) sigma
                    (maintained q))
                  (And (sufficient q sigma d) (usesToRealize q d sigma))) →
          @Exists.{apfNative_u_2 + 1} P fun (pq : P) =>
            And
              (∀ (d : D),
                @Membership.mem.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
                    (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1} (Finset.{apfNative_u_1} D) D
                      (@Finset.instSetLike.{apfNative_u_1} D))
                    (@Union.union.{apfNative_u_1} (Finset.{apfNative_u_1} D) (@Finset.instUnion.{apfNative_u_1} D inst)
                      S T)
                    d →
                  @Exists.{apfNative_u_4 + 1} (Set.{apfNative_u_4} Record) fun (sigma : Set.{apfNative_u_4} Record) =>
                    And
                      (@LE.le.{apfNative_u_4} (Set.{apfNative_u_4} Record) (@Set.instLE.{apfNative_u_4} Record) sigma
                        (maintained pq))
                      (And (sufficient pq sigma d) (usesToRealize pq d sigma)))
              (@LE.le.{0} Real Real.instLE (NNReal.toReal (calibration (wholeResource pq)))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (NNReal.toReal (calibration (wholeResource p))) (NNReal.toReal (calibration (wholeResource q)))))),
  @LE.le.{0} Real Real.instLE
    (@APFPaper1.Source.familyCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
      wholeResource calibration maintained sufficient usesToRealize
      (@Union.union.{apfNative_u_1} (Finset.{apfNative_u_1} D) (@Finset.instUnion.{apfNative_u_1} D inst) S T))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@APFPaper1.Source.familyCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
        wholeResource calibration maintained sufficient usesToRealize S)
      (@APFPaper1.Source.familyCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
        wholeResource calibration maintained sufficient usesToRealize T)) := by
  exact @APFPaper1.Source.familyCost_union_le_of_join
