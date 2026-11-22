-- Prove2me | solution 1 for Auto.carlesonMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:00:00.339966+00:00
-- url     : https://prove2.me/submissions/450e25a8-e9c0-48be-a6f1-731946d5f835

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
theorem _root_.solution : 0 < carlesonMass := carlesonBump₀.integral_pos
end Auto
