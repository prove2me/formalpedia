-- Prove2me | solution 1 for Auto.carlesonBump_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:25:28.972732+00:00
-- url     : https://prove2.me/submissions/9f7ac206-0c0a-4956-a9fb-6c2f9c8b04e4

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
theorem _root_.solution (b : ContDiffBump (0 : ℝ)) {x : ℝ} (hx : b.rOut ≤ |x|) : b x = 0 :=
  b.zero_of_le_dist (by simpa [Real.dist_eq] using hx)
end Auto
