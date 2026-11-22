-- Prove2me | solution 1 for Auto.measurable_carlesonWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:00:02.824003+00:00
-- url     : https://prove2.me/submissions/b1134de1-1dc4-4b2d-b61f-c757e5503ec6

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_continuous_carlesonW

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution : Measurable carlesonWeight :=
  (continuous_carlesonW.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))).measurable
end Auto
