-- Prove2me | solution 1 for Auto.Icc_succ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:51:31.11305+00:00
-- url     : https://prove2.me/submissions/58523923-06f0-48b9-bc30-0f92d9146181

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
open Real
namespace Auto
theorem _root_.solution (N : ℕ) :
    Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
      insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) N)) := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_insert]
  push_cast
  omega
end Auto
