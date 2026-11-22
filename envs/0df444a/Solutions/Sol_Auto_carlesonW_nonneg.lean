-- Prove2me | solution 1 for Auto.carlesonW_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:58:47.831242+00:00
-- url     : https://prove2.me/submissions/038b160d-bab4-4adc-a072-ab08bc0c7023

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution (t u : ℝ) : 0 ≤ carlesonW t u := by
  unfold carlesonW
  have := carlesonBump₀.nonneg (x := u)
  have := carlesonBump₁.nonneg (x := 2 * u - t)
  have := carlesonBump₁.nonneg (x := t - u)
  positivity
end Auto
