-- Prove2me | solution 1 for APFPaper5.K1.CheapBook.cheap_cost_all
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:44:36.099752+00:00
-- url     : https://prove2.me/submissions/2714894a-0639-450e-b0a3-54a98fe1905d

import Definitions.Def_APFPaper5_K1_shared_record_books_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_shared_record_books
title: Two record books with shared records: in one, any number of distinctions ride one record at one cost and the form has one direction; in the other, three distinctions with no private record have a faithful form while their cost over the marginal floor is 2.1
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:3612 (Example, shared coarse record), 1824 and 2753 (the increment of a
 derived discriminator vanishes), 1826 (the count "concerns support-novel increments, not all predicates,
 state labels, or a representation's dimension"), 3124-3131 (the merge prescription). Paper 5 Supplement
 v7.33:232-238 (two forms of finite rank; the uniform bound on dimension is the stronger one).
 Def_APFPaper5_K1_RecordModel (seat 01WrrBvu): the model where every finite set of records is a protocol.
 Thm_APFPaper5_K1_table_kernel_and_support and Thm_APFPaper1_supportNovel_of_private_record (this seat).
 Thm_APFPaper5_K1_records_meet_continuity_at_resolution (seat 01WrrBvu): its fineness floor assumes every
 distinction of a region is charged a floor, and does not claim it.
consumes_inputs: none. These are record books (source data of the family-cost definition), NOT worlds
 meeting the eight declared forms: no states, continuations or alignments are supplied.
named_hypotheses: none.
statement: (recordModel_supportNovel_iff) in the record model with every record of positive cost, d is
 support-novel over S exactly when d needs a record S does not need.
 COARSE BOOK, n distinctions, one record of cost 1 needed by all: (coarse_cost) every nonempty family costs
 1, whatever n is. (coarse_marginal_zero) adding a distinction to a nonempty family adds nothing.
 (coarse_not_novel) no distinction is support-novel over a nonempty family. (coarse_score) every two
 distinctions score 1, the same as each scores with itself. (coarse_not_faithful) for n at least 2 the form
 is not faithful.
 CHEAP-SHARED BOOK, three distinctions needing {a,b,c}, {a,b}, {a,c}, with a costing 1/10 and b, c costing
 1: (cheap_no_private) no distinction has a record the others do not need. (cheap_faithful) the form is
 faithful. (cheap_floor) every support-novel addition raises the cost by at least 1. (cheap_cost_all) the
 three together cost 21/10. So three independent directions sit at capacity over floor 2.1.
not_claimed: that either book is a world of the framework, or that either is excluded. That the coarse book's
 n distinctions are n distinctions in the Supplement's counting sense: by the Supplement's own prescription
 they merge. No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or
 that Born is derived.
-/
import Definitions.Def_APFPaper5_K1_table_kernel_and_support_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_form_eq_zero_iff
import Theorems.Thm_APFPaper5_K1_atomTable_faithful_iff
import Theorems.Thm_APFPaper5_K1_atomTable_row_eq_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_merge_of_same_marks
import Theorems.Thm_APFPaper5_K1_atomTable_eq_zero_of_disjoint
import Theorems.Thm_APFPaper5_K1_card_mul_le_sum_of_private
import Theorems.Thm_APFPaper1_Source_sum_needed_le_bill
import Theorems.Thm_APFPaper1_Source_familyCost_eq_sum_of_available
import Theorems.Thm_APFPaper1_Source_supportNovel_of_private_record
import Theorems.Thm_APFPaper1_Source_supportNovel_of_private_record_count
import Theorems.Thm_APFPaper1_Source_marginal_ge_of_private_record
import Theorems.Thm_APFPaper1_Source_each_private_excludes_riding
import Theorems.Thm_APFPaper1_Source_supportNovel_of_each_private
import Theorems.Thm_APFPaper1_Source_marginal_zero_of_no_own_record
import Theorems.Thm_APFPaper1_Source_needs_own_record_of_supportNovel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source
namespace APFPaper5.K1

universe u v

/-- In the record model with every record of positive cost, support novelty over S is needing a
record that S does not need. -/
theorem recordModel_supportNovel_iff {ι : Type u} {Rec : Type v} [DecidableEq Rec]
    (w : Rec → NNReal) (hpos : ∀ a, 0 < w a) (fam : ι → Finset Rec) (S : Finset ι) (d : ι) :
    supportNovel (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
        (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Rec))
        (fun _ sigma e => (↑(fam e) : Set Rec) ⊆ sigma) (fun _ _ _ => True) S d ↔
      ¬ fam d ⊆ S.biUnion fam := by
  have hbill : ∀ p : Finset Rec, ((∑ a ∈ p, w a : NNReal) : ℝ) = ∑ r ∈ p, (w r : ℝ) :=
    fun p => NNReal.coe_sum _ _
  have havail : ∃ p : Finset Rec, p = S.biUnion fam ∧ ∀ e ∈ S, ∃ sigma : Set Rec,
      sigma ⊆ (↑p : Set Rec) ∧ (↑(fam e) : Set Rec) ⊆ sigma ∧ True :=
    ⟨S.biUnion fam, rfl, fun e he => ⟨↑(S.biUnion fam), subset_rfl,
      Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem fam he), trivial⟩⟩
  constructor
  · intro hnov
    exact needs_own_record_of_supportNovel (D := ι) (P := Finset Rec) (R := Finset Rec)
      (Record := Rec) (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Rec))
      (fun _ sigma e => (↑(fam e) : Set Rec) ⊆ sigma) (fun _ _ _ => True) (fun p => p) fam w
      hbill (fun _ => rfl) (fun _ _ _ h => h) (fun _ _ _ h => h) S d havail hnov
  · intro hpriv
    obtain ⟨a, had, haS⟩ := Finset.not_subset.mp hpriv
    exact supportNovel_of_private_record (D := ι) (P := Finset Rec) (R := Finset Rec)
      (Record := Rec) (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Rec))
      (fun _ sigma e => (↑(fam e) : Set Rec) ⊆ sigma) (fun _ _ _ => True) (fun p => p) fam w
      hbill (fun _ => rfl) (fun _ _ _ h => h) S d havail a had haS (hpos a)

/-! ### The coarse book: n distinctions, one record -/

namespace CoarseBook





theorem biUnion_of_nonempty (n : ℕ) (S : Finset (Fin n)) (hS : S.Nonempty) :
    S.biUnion (fam n) = {()} := by
  obtain ⟨d, hd⟩ := hS
  apply Finset.Subset.antisymm
  · intro r _
    exact Finset.mem_singleton.mpr rfl
  · intro r hr
    exact Finset.mem_biUnion.mpr ⟨d, hd, hr⟩

/-- Every nonempty family costs 1, whatever n is. -/
theorem coarse_cost (n : ℕ) (S : Finset (Fin n)) (hS : S.Nonempty) :
    recordModelCost w (fam n) S = 1 := by
  rw [recordModelCost_eq, biUnion_of_nonempty n S hS]
  simp [w]

/-- Adding a distinction to a nonempty family adds nothing to the cost. -/
theorem coarse_marginal_zero (n : ℕ) (S : Finset (Fin n)) (hS : S.Nonempty) (d : Fin n) :
    recordModelCost w (fam n) (insert d S) = recordModelCost w (fam n) S := by
  rw [coarse_cost n S hS, coarse_cost n (insert d S) (Finset.insert_nonempty d S)]

/-- No distinction is support-novel over a nonempty family. -/
theorem coarse_not_novel (n : ℕ) (S : Finset (Fin n)) (hS : S.Nonempty) (d : Fin n) :
    ¬ supportNovel (D := Fin n) (P := Finset Unit) (R := Finset Unit) (Record := Unit)
        (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Unit))
        (fun _ sigma e => (↑(fam n e) : Set Unit) ⊆ sigma) (fun _ _ _ => True) S d := by
  rw [recordModel_supportNovel_iff w (fun _ => one_pos) (fam n) S d, not_not,
    biUnion_of_nonempty n S hS]
  exact Finset.Subset.refl _

/-- Every two distinctions score 1, as each does with itself. -/
theorem coarse_score (n : ℕ) (i j : Fin n) :
    sharedCost (recordModelCost w (fam n)) {i} {j} = 1 := by
  unfold sharedCost
  rw [coarse_cost n {i} (Finset.singleton_nonempty i),
    coarse_cost n {j} (Finset.singleton_nonempty j),
    coarse_cost n ({i} ∪ {j}) ⟨i, Finset.mem_union_left _ (Finset.mem_singleton_self i)⟩]
  norm_num

/-- With at least two distinctions the form is not faithful: they are one direction. -/
theorem coarse_not_faithful (n : ℕ) (hn : 2 ≤ n) :
    ¬ FaithfulNonnegDiagonal
        (tableForm (fun i j : Fin n => sharedCost (recordModelCost w (fam n)) {i} {j}))
        (LinearEquiv.refl ℝ (Fin n → ℝ)) := by
  have htab : (fun i j : Fin n => sharedCost (recordModelCost w (fam n)) {i} {j}) =
      atomTable (fun a => (w a : ℝ)) (fun k a => decide (a ∈ fam n k)) := by
    funext i j
    exact recordModel_sharedCost w (fam n) i j
  rw [htab]
  exact (atomTable_merge_of_same_marks (fun a => (w a : ℝ)) (fun a => NNReal.coe_nonneg _)
    (fun k a => decide (a ∈ fam n k)) (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)
    (by intro h; exact absurd (congrArg Fin.val h) (by norm_num)) (fun _ _ => rfl)).2

end CoarseBook

/-! ### The cheap-shared book: three distinctions, no private record, a faithful form -/

namespace CheapBook





theorem w_pos (a : Fin 3) : 0 < w a := by
  unfold w
  split_ifs <;> norm_num

theorem w_zero : ((w 0 : NNReal) : ℝ) = 1 / 10 := by
  unfold w
  simp

theorem w_ne_zero (a : Fin 3) (ha : a ≠ 0) : ((w a : NNReal) : ℝ) = 1 := by
  unfold w
  simp [ha]

/-- No distinction has a record that the others do not need. -/
theorem cheap_no_private : ∀ i : Fin 3, ¬ ∃ a : Fin 3, ∀ j : Fin 3, (a ∈ fam j ↔ j = i) := by
  decide

theorem zero_mem_fam (e : Fin 3) : (0 : Fin 3) ∈ fam e := by
  revert e
  decide

theorem fam_has_nonzero (d : Fin 3) : ∃ r ∈ fam d, r ≠ 0 := by
  revert d
  decide

theorem ind_of_mem (a k : Fin 3) (h : a ∈ fam k) : ind (decide (a ∈ fam k)) = 1 := by
  simp [ind, h]

theorem ind_of_not_mem (a k : Fin 3) (h : a ∉ fam k) : ind (decide (a ∈ fam k)) = 0 := by
  simp [ind, h]

/-- The form is faithful: the three are independent directions. -/
theorem cheap_faithful :
    FaithfulNonnegDiagonal
        (tableForm (fun i j : Fin 3 => sharedCost (recordModelCost w fam) {i} {j}))
        (LinearEquiv.refl ℝ (Fin 3 → ℝ)) := by
  have htab : (fun i j : Fin 3 => sharedCost (recordModelCost w fam) {i} {j}) =
      atomTable (fun a => (w a : ℝ)) (fun k a => decide (a ∈ fam k)) := by
    funext i j
    exact recordModel_sharedCost w fam i j
  rw [htab, atomTable_faithful_iff _ (fun a => NNReal.coe_nonneg _)]
  intro x hx
  have h0 := hx 0 (NNReal.coe_pos.mpr (w_pos 0))
  have h1 := hx 1 (NNReal.coe_pos.mpr (w_pos 1))
  have h2 := hx 2 (NNReal.coe_pos.mpr (w_pos 2))
  rw [Fin.sum_univ_three] at h0 h1 h2
  have e00 := ind_of_mem 0 0 (by decide)
  have e01 := ind_of_mem 0 1 (by decide)
  have e02 := ind_of_mem 0 2 (by decide)
  have e10 := ind_of_mem 1 0 (by decide)
  have e11 := ind_of_mem 1 1 (by decide)
  have e12 := ind_of_not_mem 1 2 (by decide)
  have e20 := ind_of_mem 2 0 (by decide)
  have e21 := ind_of_not_mem 2 1 (by decide)
  have e22 := ind_of_mem 2 2 (by decide)
  rw [e00, e01, e02] at h0
  rw [e10, e11, e12] at h1
  rw [e20, e21, e22] at h2
  funext k
  fin_cases k
  · show x 0 = 0
    linarith
  · show x 1 = 0
    linarith
  · show x 2 = 0
    linarith

/-- Every addition that needs a record the family does not need raises the cost by at least 1. -/
theorem cheap_increment (S : Finset (Fin 3)) (d : Fin 3) (hpriv : ¬ fam d ⊆ S.biUnion fam) :
    1 ≤ recordModelCost w fam (insert d S) - recordModelCost w fam S := by
  have key : ∃ r ∈ fam d, r ∉ S.biUnion fam ∧ r ≠ 0 := by
    rcases S.eq_empty_or_nonempty with rfl | ⟨e, he⟩
    · obtain ⟨r, hr, hr0⟩ := fam_has_nonzero d
      exact ⟨r, hr, by simp, hr0⟩
    · obtain ⟨r, hr, hrU⟩ := Finset.not_subset.mp hpriv
      refine ⟨r, hr, hrU, fun h0 => hrU ?_⟩
      rw [h0]
      exact Finset.mem_biUnion.mpr ⟨e, he, zero_mem_fam e⟩
  obtain ⟨r, hr, hrU, hr0⟩ := key
  rw [recordModelCost_eq, recordModelCost_eq]
  have hins : insert r (S.biUnion fam) ⊆ (insert d S).biUnion fam := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha'
    · exact Finset.mem_biUnion.mpr ⟨d, Finset.mem_insert_self _ _, hr⟩
    · obtain ⟨e, he, hae⟩ := Finset.mem_biUnion.mp ha'
      exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_insert_of_mem he, hae⟩
  have hsum : ∑ a ∈ insert r (S.biUnion fam), (w a : ℝ) ≤
      ∑ a ∈ (insert d S).biUnion fam, (w a : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hins (fun a _ _ => NNReal.coe_nonneg _)
  rw [Finset.sum_insert hrU, w_ne_zero r hr0] at hsum
  linarith

/-- B05's floor on this book is 1: every support-novel addition raises the cost by at least 1. -/
theorem cheap_floor (S : Finset (Fin 3)) (d : Fin 3)
    (hnov : supportNovel (D := Fin 3) (P := Finset (Fin 3)) (R := Finset (Fin 3))
        (Record := Fin 3) (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set (Fin 3)))
        (fun _ sigma e => (↑(fam e) : Set (Fin 3)) ⊆ sigma) (fun _ _ _ => True) S d) :
    1 ≤ recordModelCost w fam (insert d S) - recordModelCost w fam S :=
  cheap_increment S d ((recordModel_supportNovel_iff w w_pos fam S d).mp hnov)

/-- The three distinctions together cost 21/10. -/
theorem cheap_cost_all : recordModelCost w fam Finset.univ = 21 / 10 := by
  rw [recordModelCost_eq, show (Finset.univ : Finset (Fin 3)).biUnion fam = Finset.univ from by decide,
    Fin.sum_univ_three, w_zero, w_ne_zero 1 (by decide), w_ne_zero 2 (by decide)]
  norm_num

end CheapBook

end APFPaper5.K1

#print axioms APFPaper5.K1.recordModel_supportNovel_iff
#print axioms APFPaper5.K1.CoarseBook.coarse_cost
#print axioms APFPaper5.K1.CoarseBook.coarse_marginal_zero
#print axioms APFPaper5.K1.CoarseBook.coarse_not_novel
#print axioms APFPaper5.K1.CoarseBook.coarse_score
#print axioms APFPaper5.K1.CoarseBook.coarse_not_faithful
#print axioms APFPaper5.K1.CheapBook.cheap_no_private
#print axioms APFPaper5.K1.CheapBook.cheap_faithful
#print axioms APFPaper5.K1.CheapBook.cheap_increment
#print axioms APFPaper5.K1.CheapBook.cheap_floor
#print axioms APFPaper5.K1.CheapBook.cheap_cost_all


theorem solution :
@Eq.{1} Real
  (@APFPaper5.K1.recordModelCost.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.CheapBook.w
    APFPaper5.K1.CheapBook.fam
    (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 21)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 21) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))))))
    (@OfNat.ofNat.{0} Real (nat_lit 10)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))) := by
  exact @APFPaper5.K1.CheapBook.cheap_cost_all
