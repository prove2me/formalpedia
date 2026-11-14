-- Prove2me | solution 1 for APFPaper5.K1.atomTable_symm
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:05:31.087793+00:00
-- url     : https://prove2.me/submissions/70e1d0c3-76c6-4755-9764-cc5bc32374b8

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_record_book_table
title: Pair numbers read off a record book are symmetric and positive
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:3037-3041 (K1). Paper 1 Supplement v9.28:3721-3749, items (i), (ii), (v):
 a finite record space, sharp events as Boolean events on it, and one family of state weights.
 Archive results this replaces hypotheses with (read as statements, not imported):
 ReachKernel.Marks.denote_eq_evalWord and attained_words_le (n marks factor through their n-bit word;
 at most 2^n words); APFLoFStrengthening.independent_finite_atoms (every Boolean assignment on finitely
 many distinct labels is realized), which supplies the single-mark atoms assumed below in that model.
consumes_inputs: none. CONDITIONAL on a record book: a finite atom type, Boolean marks on it, and
 nonnegative weights. The earlier hypotheses "symmetric table" and "interchangeable marks" are not assumed.
statement: For atomTable w mark i j := sum over atoms a of w a * [mark i a] * [mark j a]:
 (atomTable_symm) the table is symmetric. (atomTable_form) its form at x is the weighted sum over atoms of
 (sum_i x_i [mark i a])^2. (atomTable_nonneg) with nonnegative weights the form is nonnegative.
 (atomTable_faithful) if for every mark i some atom of positive weight is marked by i alone, the form
 vanishes only at zero. (record_book_table_satisfies_K1) so the typed K1 hypotheses hold on coefficient
 vectors with the identity as role exchange. (atomTable_roleExchange) and "prepare mark i" to "test mark i"
 respects the linear relations.
not_claimed: that a physical score is such a table, i.e. that a record book exists for the interface (the
 Static-Sep branch); that the weights are counts, frequencies or anything measured; anything in the branch
 where no record book exists.
-/
import Definitions.Def_APFPaper5_K1_OrderedScore
import Definitions.Def_APFPaper5_K1_MarkTable
import Theorems.Thm_APFPaper5_K1_tableForm_symm
import Theorems.Thm_APFPaper5_K1_roleExchange_respects_null
import Theorems.Thm_APFPaper5_K1_interchangeable_posDef
import Theorems.Thm_APFPaper5_K1_tableForm_isBilinear
import Theorems.Thm_APFPaper5_K1_interchangeable_marks_satisfy_K1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1

universe u v
variable {ι : Type u} [Fintype ι] {W : Type v} [Fintype W]

omit [Fintype ι] in
theorem atomTable_symm (w : W → ℝ) (mark : ι → W → Bool) (i j : ι) :
    atomTable w mark i j = atomTable w mark j i := by
  unfold atomTable
  exact Finset.sum_congr rfl (fun a _ => by ring)

theorem atomTable_form (w : W → ℝ) (mark : ι → W → Bool) (x : ι → ℝ) :
    tableForm (atomTable w mark) x x = ∑ a, w a * (∑ i, x i * ind (mark i a)) ^ 2 := by
  unfold tableForm atomTable
  have h : ∀ i j, x i * (∑ a, w a * (ind (mark i a) * ind (mark j a))) * x j =
      ∑ a, w a * ((x i * ind (mark i a)) * (x j * ind (mark j a))) := by
    intro i j
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  simp only [h]
  calc ∑ i, ∑ j, ∑ a, w a * ((x i * ind (mark i a)) * (x j * ind (mark j a)))
      = ∑ i, ∑ a, ∑ j, w a * ((x i * ind (mark i a)) * (x j * ind (mark j a))) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ a, ∑ i, ∑ j, w a * ((x i * ind (mark i a)) * (x j * ind (mark j a))) :=
        Finset.sum_comm
    _ = ∑ a, w a * (∑ i, x i * ind (mark i a)) ^ 2 := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])

theorem atomTable_nonneg (w : W → ℝ) (hw : ∀ a, 0 ≤ w a) (mark : ι → W → Bool) (x : ι → ℝ) :
    0 ≤ tableForm (atomTable w mark) x x := by
  rw [atomTable_form]
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (hw a) (sq_nonneg _))

theorem atomTable_faithful [DecidableEq ι] (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
    (mark : ι → W → Bool)
    (hsingle : ∀ i, ∃ a, 0 < w a ∧ ∀ j, mark j a = decide (j = i))
    (x : ι → ℝ) (hx : tableForm (atomTable w mark) x x = 0) : x = 0 := by
  rw [atomTable_form] at hx
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a _ => mul_nonneg (hw a) (sq_nonneg _))).mp hx
  funext i
  obtain ⟨a, hpos, ha⟩ := hsingle i
  have h0 := hall a (Finset.mem_univ a)
  have hsq : (∑ j, x j * ind (mark j a)) ^ 2 = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (ne_of_gt hpos)
    · exact h
  have hs : ∑ j, x j * ind (mark j a) = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
  have hval : ∑ j, x j * ind (mark j a) = x i := by
    have hterm : ∀ j, x j * ind (mark j a) = if j = i then x j else 0 := by
      intro j
      rw [ha j]
      by_cases hji : j = i <;> simp [ind, hji]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hval] at hs
  exact hs

theorem atomTable_roleExchange (w : W → ℝ) (mark : ι → W → Bool) (x : ι → ℝ)
    (hx : ∀ i, ∑ j, atomTable w mark i j * x j = 0) :
    ∀ j, ∑ i, x i * atomTable w mark i j = 0 :=
  roleExchange_respects_null (atomTable w mark) (atomTable_symm w mark) x hx

theorem record_book_table_satisfies_K1 [DecidableEq ι] (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
    (mark : ι → W → Bool)
    (hsingle : ∀ i, ∃ a, 0 < w a ∧ ∀ j, mark j a = decide (j = i)) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm (atomTable w mark)) ∧
      FaithfulNonnegDiagonal (tableForm (atomTable w mark)) (LinearEquiv.refl ℝ (ι → ℝ)) :=
  ⟨tableForm_isBilinear _,
    fun x => atomTable_nonneg w hw mark x,
    fun x hx => atomTable_faithful w hw mark hsingle x hx⟩

end APFPaper5.K1


universe apfNative_u apfNative_v
theorem solution :
∀ {ι : Type apfNative_u} {W : Type apfNative_v} [inst : Fintype.{apfNative_v} W] (w : W → Real) (mark : ι → W → Bool)
  (i j : ι),
  @Eq.{1} Real (@APFPaper5.K1.atomTable.{apfNative_u, apfNative_v} ι W inst w mark i j)
    (@APFPaper5.K1.atomTable.{apfNative_u, apfNative_v} ι W inst w mark j i) := by
  exact @APFPaper5.K1.atomTable_symm
