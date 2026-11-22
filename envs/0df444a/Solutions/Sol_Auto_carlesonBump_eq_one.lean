-- Prove2me | solution 1 for Auto.carlesonBump_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:44:35.213047+00:00
-- url     : https://prove2.me/submissions/864606a4-4db6-438f-8dc0-404c60e6a172

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution (b : ContDiffBump (0 : ℝ)) {x : ℝ} (hx : |x| ≤ b.rIn) : b x = 1 :=
  b.one_of_mem_closedBall (by simpa [Real.dist_eq] using hx)
end Auto
