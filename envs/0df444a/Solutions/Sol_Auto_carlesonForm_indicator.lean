-- Prove2me | solution 1 for Auto.carlesonForm_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:52:42.581957+00:00
-- url     : https://prove2.me/submissions/6b826ba3-7bd0-4b1b-99d7-26781fab38c0

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_integrable_carlesonForm
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution {Q : Set ℝ} (hQ : MeasurableSet Q) {h : ℝ → ℂ} {ν : ℝ → ℝ}
    {B V : ℝ} (hh : Measurable h) (hν : Measurable ν) (hB : ∀ x, ‖h x‖ ≤ B)
    (hV : ∀ x, |ν x| ≤ V) (hQR : volume Q ≠ ⊤) :
    carlesonForm (Q.indicator 1) ν h = ∫ x in Q, carlesonOp h ν x := by
  have hi : Integrable fun x => Q.indicator (1 : ℝ → ℝ) x ^ 2 * |ν x| := by
    refine ((integrableOn_const (C := V) hQR).integrable_indicator hQ).mono'
      (Measurable.aestronglyMeasurable (by fun_prop (disch := exact hQ)))
      (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ Q
    · simp [hx, hV x]
    · simp [hx]
  have hint := integrable_carlesonForm (measurable_one.indicator hQ) hν hh hB hi
  rw [Measure.volume_eq_prod] at hint
  rw [carlesonForm, Measure.volume_eq_prod, integral_prod _ hint, ← integral_indicator hQ]
  congr 1
  ext x
  by_cases hx : x ∈ Q
  · simp [hx, carlesonOp]
  · simp [hx]
end Auto
