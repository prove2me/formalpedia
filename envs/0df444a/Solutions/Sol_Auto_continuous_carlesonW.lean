-- Prove2me | solution 1 for Auto.continuous_carlesonW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:58:41.873548+00:00
-- url     : https://prove2.me/submissions/919c7db8-e3e3-4929-b59f-1dc0cda0788a

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
theorem _root_.solution : Continuous fun p : ℝ × ℝ => carlesonW p.1 p.2 := by
  unfold carlesonW
  have h₀ := carlesonBump₀.continuous
  have h₁ := carlesonBump₁.continuous
  fun_prop
end Auto
