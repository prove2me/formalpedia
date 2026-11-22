-- Prove2me | solution 1 for Auto.continuous_dirichletKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:51:19.754205+00:00
-- url     : https://prove2.me/submissions/eafc1cc5-02bd-4c6b-a822-ec33d30b3d6d

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
open Real
namespace Auto
theorem _root_.solution (N : ℕ) : Continuous (dirichletKernel N) := by
  unfold dirichletKernel
  fun_prop
end Auto
