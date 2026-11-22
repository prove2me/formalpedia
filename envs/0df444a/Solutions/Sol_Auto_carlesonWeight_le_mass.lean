-- Prove2me | solution 1 for Auto.carlesonWeight_le_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:46:33.968797+00:00
-- url     : https://prove2.me/submissions/ffb73b40-7b73-417a-9d3e-c7ab7bdebcba

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_carlesonW_le
public import Theorems.Thm_Auto_integrable_carlesonW

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution (t : ℝ) : carlesonWeight t ≤ carlesonMass :=
  integral_mono (integrable_carlesonW t) carlesonBump₀.integrable (carlesonW_le t)
end Auto
