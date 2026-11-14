-- Prove2me | solution 1 for APFPaper5.K1.interchangeable_posDef
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:33:04.237801+00:00
-- url     : https://prove2.me/submissions/8119b621-d196-472f-9d9e-0a273efcc0b5

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_mark_table
title: A symmetric table of pair numbers on finitely many marks: role exchange and positivity
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:3037-3041 (K1: boundary-role isomorphism, faithful nonnegative diagonal).
consumes_inputs: none. CONDITIONAL: every hypothesis is supplied data about a real table G indexed by a
 finite set of marks. No declared input produces such a table.
statement: (tableForm_symm) a symmetric table gives a symmetric form. (roleExchange_respects_null) for a
 symmetric table, a coefficient vector that every row annihilates is annihilated in every column, so
 sending "prepare mark i" to "test mark i" respects the linear relations among the preparations.
 (interchangeable_form) if every mark scores 1 against itself and every two different marks score the
 same number c, the form is (1-c) * sum x_i^2 + c * (sum x_i)^2. (interchangeable_posDef) if moreover
 0 <= c < 1, the form is nonnegative and vanishes only at zero.
not_claimed: that a physical score is symmetric, that marks are interchangeable, or that c is a frequency;
 that the marks span the preparation space. At c = 1 the form vanishes on differences of marks.
-/
import Definitions.Def_APFPaper5_K1_MarkTable
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1

universe u
variable {ι : Type u} [Fintype ι]

theorem tableForm_symm (G : ι → ι → ℝ) (hG : ∀ i j, G i j = G j i) (x y : ι → ℝ) :
    tableForm G x y = tableForm G y x := by
  unfold tableForm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [hG i j]; ring

theorem roleExchange_respects_null (G : ι → ι → ℝ) (hG : ∀ i j, G i j = G j i) (x : ι → ℝ)
    (hx : ∀ i, ∑ j, G i j * x j = 0) : ∀ j, ∑ i, x i * G i j = 0 := by
  intro j
  rw [← hx j]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hG i j]; ring

theorem interchangeable_form [DecidableEq ι] (G : ι → ι → ℝ) (c : ℝ)
    (hG : Interchangeable G c) (x : ι → ℝ) :
    tableForm G x x = (1 - c) * ∑ i, x i ^ 2 + c * (∑ i, x i) ^ 2 := by
  unfold tableForm
  have h : ∀ i j, x i * G i j * x j =
      c * (x i * x j) + (1 - c) * (if i = j then x i * x j else 0) := by
    intro i j; rw [hG i j]; split_ifs <;> ring
  have hrow : ∀ i, ∑ j, x i * G i j * x j = c * (x i * ∑ j, x j) + (1 - c) * (x i * x i) := by
    intro i
    simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  simp only [hrow, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hsq : ∑ i, x i * x i = ∑ i, x i ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsq]; ring

theorem interchangeable_posDef [DecidableEq ι] (G : ι → ι → ℝ) (c : ℝ)
    (hG : Interchangeable G c) (h0 : 0 ≤ c) (h1 : c < 1) (x : ι → ℝ) :
    0 ≤ tableForm G x x ∧ (tableForm G x x = 0 → x = 0) := by
  rw [interchangeable_form G c hG x]
  have hs : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have ht : 0 ≤ c * (∑ i, x i) ^ 2 := mul_nonneg h0 (sq_nonneg _)
  have hc : 0 < 1 - c := by linarith
  refine ⟨by nlinarith [mul_nonneg hc.le hs], fun hz => ?_⟩
  have hprod : (1 - c) * ∑ i, x i ^ 2 = 0 := by
    have := mul_nonneg hc.le hs
    linarith
  have hsum : ∑ i, x i ^ 2 = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · exact h
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).mp hsum i
    (Finset.mem_univ i)
  exact pow_eq_zero_iff (two_ne_zero) |>.mp hi

end APFPaper5.K1


universe apfNative_u
theorem solution :
∀ {ι : Type apfNative_u} [inst : Fintype.{apfNative_u} ι] [inst_1 : DecidableEq.{apfNative_u + 1} ι] (G : ι → ι → Real)
  (c : Real) (hG : @APFPaper5.K1.Interchangeable.{apfNative_u} ι inst_1 G c)
  (h0 : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
  (h1 : @LT.lt.{0} Real Real.instLT c (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (x : ι → Real),
  And
    (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@APFPaper5.K1.tableForm.{apfNative_u} ι inst G x x))
    (@Eq.{1} Real (@APFPaper5.K1.tableForm.{apfNative_u} ι inst G x x)
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
      @Eq.{apfNative_u + 1} (ι → Real) x
        (@OfNat.ofNat.{apfNative_u} (ι → Real) (nat_lit 0)
          (@Zero.toOfNat0.{apfNative_u} (ι → Real)
            (@Pi.instZero.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instZero)))) := by
  exact @APFPaper5.K1.interchangeable_posDef
