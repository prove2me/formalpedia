-- Prove2me | solution 1 for Auto.carlesonWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:59:46.333022+00:00
-- url     : https://prove2.me/submissions/50e8dcd7-737b-4f48-b9aa-2fb875469c40

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_carlesonW_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution (t : ℝ) : 0 ≤ carlesonWeight t :=
  integral_nonneg (carlesonW_nonneg t)
end Auto
