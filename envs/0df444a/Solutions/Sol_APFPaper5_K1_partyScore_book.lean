-- Prove2me | solution 1 for APFPaper5.K1.partyScore_book
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:02:33.280811+00:00
-- url     : https://prove2.me/submissions/cac7a6bb-4054-410f-9623-374c98d0c03f

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_party_score
title: In a book with shared and joint records a distinction is party to exactly the records the book lists it against; the party score is the record-book table; it meets K1's typed conditions when no record has negative cost and each distinction has a record of its own of positive cost, and exactly when no nonzero combination is cancelled by every record of positive cost; with no joint record it is the shared cost
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 22:13 HST: "B" (RULING_K1_score_with_joint_records_2026-11-14).
 Def_APFPaper5_K1_PartyScore. Builder seat: atomTable, tableForm, record_book_table_satisfies_K1,
 sharedCost. This seat: atomTable_faithful_iff (pass 18).
standing: THEOREMS ON A DEFINITION. No input is consumed. The K1 statement has two premises: no record of
 negative cost, and each distinction has a record of its own of positive cost. NEITHER IS DERIVED from the
 eight for a book with joint records (see "what this file does NOT say").
what this file says:
 - partyTo_book_iff: under the two-kind keeping rule, "party to" as typed is exactly the book's listing,
   for shared and for joint records alike. So a joint record is counted like a shared one.
 - partyScore_book: the party score of such a book is the builder seat's record-book table.
 - partyScore_book_meets_K1: K1's typed conditions, from the two premises.
 - partyScore_book_faithful_iff: the exact condition for the faithful nonnegative diagonal.
 - sharedCost_eq_partyScore_of_no_joint: with no joint record the shared cost of two distinctions IS
   their party score. So ruling B agrees with call 1 of 19:57 HST wherever there is no joint record.
what this file does NOT say:
 - That the declared B05 gives each counted distinction a record of its own in a book with joint records.
   NOT DERIVED. Under the joint rule what a distinction adds over the rest includes the joint records it
   is party to (instance: Thm_APFPaper5_K1_joint_pair_two_tables, jointRule_recordTable_reads), so the
   floor no longer singles out a record of its own. The pass-29 route used the shared rule at that step.
 - The general formula for the shared cost with joint records (it nets the two kinds). Typed only in the
   two-distinction instance.
 - That a cost fixes its book. It does not where both kinds are present.
 - That any world meeting the eight carries such a book with the premises. None is built.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_PartyScore
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Definitions.Def_APFPaper5_K1_table_kernel_and_support_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_form_eq_zero_iff
import Theorems.Thm_APFPaper5_K1_atomTable_faithful_iff
import Theorems.Thm_APFPaper5_K1_atomTable_row_eq_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_merge_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_eq_zero_of_disjoint
import Theorems.Thm_APFPaper5_K1_card_mul_le_sum_of_private
import Theorems.Thm_APFPaper5_K1_sharedCost_self
import Theorems.Thm_APFPaper5_K1_sharedCost_le_right
import Theorems.Thm_APFPaper5_K1_sharedCost_le_left
import Theorems.Thm_APFPaper5_K1_sharedCost_nonneg_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_ledger
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_no_joint
import Theorems.Thm_APFPaper5_K1_cost_is_count_times_floor

set_option autoImplicit false

namespace APFPaper5.K1

universe u v
variable {D : Type u} [Fintype D] [DecidableEq D] {W : Type v}

/-- Under the two-kind keeping rule a distinction is party to exactly the records listed against it. -/
theorem partyTo_book_iff (mark : D → W → Bool) (joint : W → Bool) (d : D) (a : W) :
    PartyTo (keepsB mark joint) d a ↔ mark d a = true := by
  constructor
  · rintro ⟨S, h1, h2⟩
    unfold keepsB at h1 h2
    by_cases hj : joint a = true
    · rw [if_pos hj] at h1 h2
      have h1' : ∀ i, mark i a = true → i ∈ insert d S := of_decide_eq_true h1
      have h2' : ¬ ∀ i, mark i a = true → i ∈ S := of_decide_eq_false h2
      by_contra hd
      apply h2'
      intro i hi
      rcases Finset.mem_insert.mp (h1' i hi) with h | h
      · rw [h] at hi
        exact absurd hi hd
      · exact h
    · rw [if_neg hj] at h1 h2
      obtain ⟨i, hiS, hi⟩ : ∃ i ∈ insert d S, mark i a = true := of_decide_eq_true h1
      have h2' : ¬ ∃ i ∈ S, mark i a = true := of_decide_eq_false h2
      rcases Finset.mem_insert.mp hiS with h | h
      · rw [h] at hi
        exact hi
      · exact absurd ⟨i, h, hi⟩ h2'
  · intro hd
    by_cases hj : joint a = true
    · refine ⟨(Finset.univ.filter (fun i => mark i a = true)).erase d, ?_, ?_⟩
      · unfold keepsB
        rw [if_pos hj]
        apply decide_eq_true
        intro i hi
        by_cases hid : i = d
        · rw [hid]
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨hid, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)
      · unfold keepsB
        rw [if_pos hj]
        apply decide_eq_false
        intro h
        exact (Finset.mem_erase.mp (h d hd)).1 rfl
    · refine ⟨∅, ?_, ?_⟩
      · unfold keepsB
        rw [if_neg hj]
        apply decide_eq_true
        exact ⟨d, Finset.mem_insert_self _ _, hd⟩
      · unfold keepsB
        rw [if_neg hj]
        apply decide_eq_false
        rintro ⟨i, hi, _⟩
        simp at hi

theorem partyMark_book (mark : D → W → Bool) (joint : W → Bool) :
    partyMark (keepsB mark joint) = mark := by
  funext d a
  unfold partyMark
  have hiff := partyTo_book_iff mark joint d a
  by_cases h : mark d a = true
  · rw [h]
    exact @decide_eq_true _ (Classical.propDecidable _) (hiff.mpr h)
  · have hf : mark d a = false := by simpa using h
    rw [hf]
    exact @decide_eq_false _ (Classical.propDecidable _) (fun hp => h (hiff.mp hp))

variable [Fintype W]

/-- The party score of a two-kind book is the record-book table of its listing. -/
theorem partyScore_book (w : W → ℝ) (mark : D → W → Bool) (joint : W → Bool) :
    partyScore w (keepsB mark joint) = atomTable w mark := by
  funext i j
  unfold partyScore
  rw [partyMark_book]

/-- K1's typed conditions for the party score: no record of negative cost, and each distinction has a
record of its own of positive cost. Shared or joint, any number of distinctions. -/
theorem partyScore_book_meets_K1 (w : W → ℝ) (hw : ∀ a, 0 ≤ w a) (mark : D → W → Bool)
    (joint : W → Bool) (hown : ∀ i, ∃ a, 0 < w a ∧ ∀ j, mark j a = decide (j = i)) :
    IsBilinear (VP := D → ℝ) (VE := D → ℝ) (tableForm (partyScore w (keepsB mark joint))) ∧
      FaithfulNonnegDiagonal (tableForm (partyScore w (keepsB mark joint)))
        (LinearEquiv.refl ℝ (D → ℝ)) := by
  rw [partyScore_book]
  exact record_book_table_satisfies_K1 w hw mark hown

/-- The exact condition: the diagonal is nonnegative and faithful exactly when no nonzero combination of
the distinctions is cancelled by every record of positive cost. -/
theorem partyScore_book_faithful_iff (w : W → ℝ) (hw : ∀ a, 0 ≤ w a) (mark : D → W → Bool)
    (joint : W → Bool) :
    FaithfulNonnegDiagonal (tableForm (partyScore w (keepsB mark joint))) (LinearEquiv.refl ℝ (D → ℝ)) ↔
      ∀ x : D → ℝ, (∀ a, 0 < w a → ∑ i, x i * ind (mark i a) = 0) → x = 0 := by
  rw [partyScore_book]
  exact atomTable_faithful_iff w hw mark

/-- With no joint record the shared cost of two distinctions is their party score. -/
theorem sharedCost_eq_partyScore_of_no_joint (w : W → ℝ) (mark : D → W → Bool) (joint : W → Bool)
    (hnone : ∀ a, joint a = false) (i j : D) :
    sharedCost (keptCost w (keepsB mark joint)) {i} {j} = partyScore w (keepsB mark joint) i j := by
  have hs : ∀ (k : D) (a : W), keepsB mark joint {k} a = mark k a := by
    intro k a
    unfold keepsB
    rw [hnone a, if_neg Bool.false_ne_true, Bool.eq_iff_iff, decide_eq_true_iff]
    constructor
    · rintro ⟨k', hk, hm⟩
      rw [Finset.mem_singleton.mp hk] at hm
      exact hm
    · intro h
      exact ⟨k, Finset.mem_singleton_self k, h⟩
  have hu : ∀ a : W, keepsB mark joint ({i} ∪ {j}) a = (mark i a || mark j a) := by
    intro a
    unfold keepsB
    rw [hnone a, if_neg Bool.false_ne_true, Bool.eq_iff_iff, decide_eq_true_iff, Bool.or_eq_true]
    constructor
    · rintro ⟨k, hk, hm⟩
      rcases Finset.mem_union.mp hk with h | h
      · rw [Finset.mem_singleton.mp h] at hm
        exact Or.inl hm
      · rw [Finset.mem_singleton.mp h] at hm
        exact Or.inr hm
    · rintro (h | h)
      · exact ⟨i, Finset.mem_union_left _ (Finset.mem_singleton_self i), h⟩
      · exact ⟨j, Finset.mem_union_right _ (Finset.mem_singleton_self j), h⟩
  rw [partyScore_book]
  unfold sharedCost keptCost atomTable
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [hs, hs, hu]
  cases mark i a <;> cases mark j a <;> simp [ind]

end APFPaper5.K1


universe apfNative_u apfNative_v
theorem solution :
∀ {D : Type apfNative_u} [inst : Fintype.{apfNative_u} D] [inst_1 : DecidableEq.{apfNative_u + 1} D]
  {W : Type apfNative_v} [inst_2 : Fintype.{apfNative_v} W] (w : W → Real) (mark : D → W → Bool) (joint : W → Bool),
  @Eq.{apfNative_u + 1} ((i j : D) → Real)
    (@APFPaper5.K1.partyScore.{apfNative_u, apfNative_v} D W inst inst_1 inst_2 w
      (@APFPaper5.K1.keepsB.{apfNative_u, apfNative_v} D W inst inst_1 mark joint))
    (@APFPaper5.K1.atomTable.{apfNative_u, apfNative_v} D W inst_2 w mark) := by
  exact @APFPaper5.K1.partyScore_book
