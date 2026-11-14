-- Prove2me | solution 1 for APFPaper5.K1.tableForm_isBilinear
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:02:31.118218+00:00
-- url     : https://prove2.me/submissions/00d189ef-1d85-4761-9813-6f4be3c75ed1

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_mark_table_instance
title: Interchangeable marks satisfy the typed K1 hypotheses
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:3037-3041 (K1); the typed hypotheses of Def_APFPaper5_K1_OrderedScore.
consumes_inputs: none. CONDITIONAL on a supplied table. This is an instance: it shows the typed K1
 hypotheses can hold together. It derives nothing about a physical score.
statement: (tableForm_isBilinear) the form of any real table on finitely many marks is bilinear.
 (interchangeable_marks_satisfy_K1) if every mark scores 1 against itself and every two different marks
 score the same c with 0 <= c < 1, then on coefficient vectors the form is bilinear and, with the identity
 as role exchange, has a nonnegative diagonal that vanishes only at zero.
-/
import Definitions.Def_APFPaper5_K1_OrderedScore
import Theorems.Thm_APFPaper5_K1_tableForm_symm
import Theorems.Thm_APFPaper5_K1_roleExchange_respects_null
import Theorems.Thm_APFPaper5_K1_interchangeable_posDef
import Mathlib.Algebra.Module.Pi

set_option autoImplicit false
namespace APFPaper5.K1

universe u
variable {ι : Type u} [Fintype ι]

theorem tableForm_isBilinear (G : ι → ι → ℝ) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm G) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e e' p; unfold tableForm
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  · intro r e p; unfold tableForm
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  · intro e p p'; unfold tableForm
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  · intro r e p; unfold tableForm
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem interchangeable_marks_satisfy_K1 [DecidableEq ι] (G : ι → ι → ℝ) (c : ℝ)
    (hG : Interchangeable G c) (h0 : 0 ≤ c) (h1 : c < 1) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm G) ∧
      FaithfulNonnegDiagonal (tableForm G) (LinearEquiv.refl ℝ (ι → ℝ)) :=
  ⟨tableForm_isBilinear G,
    fun x => (interchangeable_posDef G c hG h0 h1 x).1,
    fun x hx => (interchangeable_posDef G c hG h0 h1 x).2 hx⟩

end APFPaper5.K1


universe apfNative_u
theorem solution :
∀ {ι : Type apfNative_u} [inst : Fintype.{apfNative_u} ι] (G : ι → ι → Real),
  @APFPaper5.K1.IsBilinear.{apfNative_u, apfNative_u} (ι → Real) (ι → Real)
    (@Pi.addCommGroup.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
    (@Pi.Function.module.{apfNative_u, 0, 0} ι Real Real Real.semiring
      (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
      (@Semiring.toModule.{0} Real Real.semiring))
    (@Pi.addCommGroup.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
    (@Pi.Function.module.{apfNative_u, 0, 0} ι Real Real Real.semiring
      (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
      (@Semiring.toModule.{0} Real Real.semiring))
    (@APFPaper5.K1.tableForm.{apfNative_u} ι inst G) := by
  exact @APFPaper5.K1.tableForm_isBilinear
