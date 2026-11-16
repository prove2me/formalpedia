-- Prove2me | solution 1 for APFPaper5.K1.atomTable_eq_zero_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:30:09.838826+00:00
-- url     : https://prove2.me/submissions/59bb18ee-589b-4435-ae84-9e685edd8330

import Definitions.Def_APFPaper5_K1_RecordModel
import Definitions.Def_APFPaper5_K1_SharedCost
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Definitions.Def_APFPaper5_K1_table_kernel_and_support_Vocabulary
import Theorems.Thm_APFPaper5_K1_familyCost_weighted
import Theorems.Thm_APFPaper5_K1_recordModelCost_eq
import Theorems.Thm_APFPaper5_K1_recordModel_sharedCost
import Theorems.Thm_APFPaper5_K1_recordModel_satisfies_K1
import Mathlib.Tactic.Ring
/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_weighted_record_model
title: In the weighted record model the family cost is the weight of the records needed, the shared cost is the weight of the shared records, and K1's record-book conditions hold
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K1_RecordModel and Def_APFPaper5_K1_SharedCost.
consumes_inputs: none. Theorems about a MODEL of the source vocabulary.
statement: (familyCost_weighted, recordModelCost_eq) the family cost of S is the total cost of the records its
 members need. (atomTable_eq_sum_inter) the atom table of membership marks is the weight of shared records.
 (sharedCost_weighted_eq_atomTable, recordModel_sharedCost) the shared cost of two single families is that
 atom table. (recordModel_satisfies_K1) if every family has a record of positive cost that no other family
 needs, the table of shared costs is bilinear with a faithful nonnegative diagonal.
 Record costs need not be equal: no clause says cost depends only on the number of records.
not_claimed: that any interface is a record model; the boundary-role isomorphism beyond the identity map; K1.
-/











set_option autoImplicit false
open APFPaper1.Source
namespace APFPaper5.K1

universe u v
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec]





theorem atomTable_eq_sum_inter [Fintype Rec] (w : Rec → ℝ) (fam : ι → Finset Rec) (i j : ι) :
    atomTable w (fun k a => decide (a ∈ fam k)) i j = ∑ a ∈ fam i ∩ fam j, w a := by
  have hterm : ∀ a : Rec, w a * (ind (decide (a ∈ fam i)) * ind (decide (a ∈ fam j))) =
      if a ∈ fam i ∩ fam j then w a else 0 := by
    intro a
    by_cases h1 : a ∈ fam i <;> by_cases h2 : a ∈ fam j <;> simp [ind, Finset.mem_inter, h1, h2]
  unfold atomTable
  simp only [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter]







end APFPaper5.K1


/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_table_kernel_and_support
title: The form of a record-book table vanishes exactly on the combinations every positively weighted record cancels; marks with the same records merge, marks with disjoint records score zero, and a family with a private record of cost at least eps per member numbers at most its cost over eps
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:358-366 and 383-388 (the pairing of K1 is taken on the quotient by the
 left and right radicals: "contextual score-null relations lie in its radicals"), 3037-3041 (K1: a faithful
 nonnegative diagonal). Paper 1 Supplement v9.28:2502-2516 (Definition, support-independent resolution:
 exact witness supports, ORTHOGONALITY "the supports are pairwise disjoint", support-local additive
 accounting), 3124-3131 (two formal distinctions reading digits of one maintained register "merge, and the
 counting theorem charges one floor, not two"), 3612 (Example, shared coarse record), 1202 ("cardinality
 counting overcharges; use chain rank").
 Thm_APFPaper5_K1_record_book_table (seat 01WrrBvu): atomTable_form, atomTable_nonneg, and atomTable_faithful
 under a single-mark atom per mark. Thm_APFPaper5_K1_weighted_record_model (seat 01WrrBvu):
 atomTable_eq_sum_inter. Thm_APFPaper5_K1_records_meet_continuity_at_resolution (seat 01WrrBvu),
 resolution_floor_of_capacity, whose hypothesis n * eps <= C is supplied here by card_mul_le_sum_of_private.
 Codebank: nothing on the kernel of a shared-cost table (apf/aboutness_occupancy_section.py uses "radical"
 for a different object).
consumes_inputs: none. Ordinary mathematics on a record book: a finite type of atoms (records), Boolean
 marks on it, nonnegative weights.
named_hypotheses: none beyond the record book. In card_mul_le_sum_of_private, hpriv (each member of the
 family has a record of cost at least eps that no other member needs) is a hypothesis on the family in
 hand.
statement: (atomTable_form_eq_zero_iff) with nonnegative weights, the form vanishes at x exactly when, at
 every atom of positive weight, the x-weighted count of the marks holding it is zero.
 (atomTable_faithful_iff) so the diagonal is faithful exactly when no nonzero x is cancelled at every atom
 of positive weight. (atomTable_row_eq_of_same_marks) two marks that hold the same atoms of positive weight
 have the same row. (atomTable_merge_of_same_marks) and the form vanishes at their difference (markDiff), which is not
 zero: the table is not faithful, and the two are one direction after the quotient.
 (atomTable_eq_zero_of_disjoint) two marks with no record in common score zero.
 (card_mul_le_sum_of_private) if each member of S has a record of cost at least eps that no other member
 needs, the size of S times eps is at most the cost of the records S needs.
not_claimed: that a physical score is a record-book table; that any family of distinctions has private or
 disjoint records. No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed,
 or that Born is derived.
-/












set_option autoImplicit false
namespace APFPaper5.K1

universe u v
variable {ι : Type u} [Fintype ι] {W : Type v} [Fintype W]

/-- The form vanishes at x exactly when every positively weighted atom cancels x. -/
theorem atomTable_form_eq_zero_iff (w : W → ℝ) (hw : ∀ a, 0 ≤ w a) (mark : ι → W → Bool)
    (x : ι → ℝ) :
    tableForm (atomTable w mark) x x = 0 ↔ ∀ a, 0 < w a → ∑ i, x i * ind (mark i a) = 0 := by
  rw [atomTable_form]
  have hnn : ∀ a ∈ (Finset.univ : Finset W), 0 ≤ w a * (∑ i, x i * ind (mark i a)) ^ 2 :=
    fun a _ => mul_nonneg (hw a) (sq_nonneg _)
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h a ha
    have h0 := h a (Finset.mem_univ a)
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (ne_of_gt ha)
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp h1
  · intro h a _
    rcases (hw a).lt_or_eq with ha | ha
    · rw [h a ha]
      ring
    · rw [← ha]
      ring

/-- The diagonal is faithful exactly when no nonzero x is cancelled at every atom of positive
weight. -/
theorem atomTable_faithful_iff (w : W → ℝ) (hw : ∀ a, 0 ≤ w a) (mark : ι → W → Bool) :
    FaithfulNonnegDiagonal (tableForm (atomTable w mark)) (LinearEquiv.refl ℝ (ι → ℝ)) ↔
      ∀ x : ι → ℝ, (∀ a, 0 < w a → ∑ i, x i * ind (mark i a) = 0) → x = 0 := by
  constructor
  · intro h x hx
    exact h.2 x ((atomTable_form_eq_zero_iff w hw mark x).mpr hx)
  · intro h
    exact ⟨fun x => atomTable_nonneg w hw mark x,
      fun x hx => h x ((atomTable_form_eq_zero_iff w hw mark x).mp hx)⟩

omit [Fintype ι] in
/-- Two marks that hold the same atoms of positive weight have the same row of the table. -/
theorem atomTable_row_eq_of_same_marks (w : W → ℝ) (mark : ι → W → Bool) (i j : ι)
    (hsame : ∀ a, w a ≠ 0 → mark i a = mark j a) (k : ι) :
    atomTable w mark i k = atomTable w mark j k := by
  unfold atomTable
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases ha : w a = 0
  · rw [ha]
    ring
  · rw [hsame a ha]



/-- Two different marks that hold the same atoms of positive weight merge: the form vanishes at
their difference, so the table is not faithful. -/
theorem atomTable_merge_of_same_marks [DecidableEq ι] (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
    (mark : ι → W → Bool) (i j : ι) (hij : i ≠ j)
    (hsame : ∀ a, 0 < w a → mark i a = mark j a) :
    tableForm (atomTable w mark) (markDiff i j) (markDiff i j) = 0 ∧
      ¬ FaithfulNonnegDiagonal (tableForm (atomTable w mark)) (LinearEquiv.refl ℝ (ι → ℝ)) := by
  have hzero : tableForm (atomTable w mark) (markDiff i j) (markDiff i j) = 0 := by
    rw [atomTable_form_eq_zero_iff w hw mark]
    intro a ha
    have hsplit : ∀ k : ι, markDiff i j k * ind (mark k a) =
        (if k = i then ind (mark k a) else 0) - (if k = j then ind (mark k a) else 0) := by
      intro k
      unfold markDiff
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq', hsame a ha]
    simp
  refine ⟨hzero, fun hf => ?_⟩
  have h0 : markDiff i j = 0 := hf.2 _ hzero
  have h1 : markDiff i j i = 0 := by rw [h0]; rfl
  simp [markDiff, hij] at h1

omit [Fintype ι] in
/-- Two marks with no record in common score zero. -/
theorem atomTable_eq_zero_of_disjoint [DecidableEq W] (w : W → ℝ) (fam : ι → Finset W) (i j : ι)
    (hdisj : Disjoint (fam i) (fam j)) :
    atomTable w (fun k a => decide (a ∈ fam k)) i j = 0 := by
  rw [atomTable_eq_sum_inter, Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.sum_empty]

omit [Fintype ι] [Fintype W] in
/-- If each member of S has a record of cost at least eps that no other member needs, the size of S
times eps is at most the cost of the records S needs. -/
theorem card_mul_le_sum_of_private [DecidableEq W] [DecidableEq ι] (w : W → ℝ)
    (hw : ∀ a, 0 ≤ w a) (fam : ι → Finset W) (S : Finset ι) (eps : ℝ)
    (hpriv : ∀ d ∈ S, ∃ a ∈ fam d, eps ≤ w a ∧ ∀ e ∈ S, e ≠ d → a ∉ fam e) :
    (S.card : ℝ) * eps ≤ ∑ a ∈ S.biUnion fam, w a := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨d0, hd0⟩
  · simp
  have : Nonempty W := ⟨(hpriv d0 hd0).choose⟩
  choose! f hf using hpriv
  have hinj : Set.InjOn f (↑S : Set ι) := by
    intro d hd e he hde
    by_contra hne
    exact (hf e he).2.2 d hd hne (hde ▸ (hf d hd).1)
  have hsub : S.image f ⊆ S.biUnion fam := by
    intro a ha
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_biUnion.mpr ⟨d, hd, (hf d hd).1⟩
  calc (S.card : ℝ) * eps = ∑ _d ∈ S, eps := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ d ∈ S, w (f d) := Finset.sum_le_sum (fun d hd => (hf d hd).2.1)
    _ = ∑ a ∈ S.image f, w a := (Finset.sum_image hinj).symm
    _ ≤ ∑ a ∈ S.biUnion fam, w a :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => hw a)

end APFPaper5.K1

#print axioms APFPaper5.K1.atomTable_form_eq_zero_iff
#print axioms APFPaper5.K1.atomTable_faithful_iff
#print axioms APFPaper5.K1.atomTable_row_eq_of_same_marks
#print axioms APFPaper5.K1.atomTable_merge_of_same_marks
#print axioms APFPaper5.K1.atomTable_eq_zero_of_disjoint
#print axioms APFPaper5.K1.card_mul_le_sum_of_private


universe apfNative_u apfNative_v
theorem solution :
∀ {ι : Type apfNative_u} {W : Type apfNative_v} [inst : Fintype.{apfNative_v} W]
  [inst_1 : DecidableEq.{apfNative_v + 1} W] (w : W → Real) (fam : ι → Finset.{apfNative_v} W) (i j : ι)
  (hdisj :
    @Disjoint.{apfNative_v} (Finset.{apfNative_v} W) (@Finset.instPartialOrder.{apfNative_v} W)
      (@Finset.instOrderBot.{apfNative_v} W) (fam i) (fam j)),
  @Eq.{1} Real
    (@APFPaper5.K1.atomTable.{apfNative_u, apfNative_v} ι W inst w
      (fun (k : ι) (a : W) =>
        @Decidable.decide
          (@Membership.mem.{apfNative_v, apfNative_v} W (Finset.{apfNative_v} W)
            (@SetLike.instMembership.{apfNative_v, apfNative_v} (Finset.{apfNative_v} W) W
              (@Finset.instSetLike.{apfNative_v} W))
            (fam k) a)
          (@Finset.decidableMem.{apfNative_v} W inst_1 a (fam k)))
      i j)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) := by
  exact @APFPaper5.K1.atomTable_eq_zero_of_disjoint
