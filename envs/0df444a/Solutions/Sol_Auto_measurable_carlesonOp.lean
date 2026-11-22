-- Prove2me | solution 1 for Auto.measurable_carlesonOp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:52:18.33548+00:00
-- url     : https://prove2.me/submissions/06246c51-20ab-4b67-b769-ac4e661eede3

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_measurable_carlesonWeight

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution {h : ℝ → ℂ} {ν : ℝ → ℝ} (hh : Measurable h) (hν : Measurable ν) :
    Measurable (carlesonOp h ν) := by
  have hw := measurable_carlesonWeight
  have hm : Measurable fun p : ℝ × ℝ =>
      h (p.1 - p.2) * ((carlesonWeight p.2 * Real.sin (ν p.1 * p.2) / p.2 : ℝ) : ℂ) := by
    fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
end Auto
