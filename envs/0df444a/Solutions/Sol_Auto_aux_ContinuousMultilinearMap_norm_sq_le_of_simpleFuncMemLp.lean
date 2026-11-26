-- Prove2me | solution 1 for Auto.aux_ContinuousMultilinearMap_norm_sq_le_of_simpleFuncMemLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:28.057687+00:00
-- url     : https://prove2.me/submissions/e4dd1148-2b7e-4edf-a547-1b15950b1a22

module
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Definitions.Def_LeanNct_Auto_MultilinearInterpolation
public import Theorems.Thm_Auto_aux_denseRange_simpleFuncMemLpToLp
public import Theorems.Thm_Auto_aux_ContinuousMultilinearMap_norm_sq_le_of_denseRange_functions

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution
    {ι X F : Type*} [Fintype ι] [MeasurableSpace X]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (p : ι → ℝ≥0∞) (μ : Measure X) [∀ i, Fact (1 ≤ p i)]
    (hp_top : ∀ i, p i ≠ ∞)
    (B : ContinuousMultilinearMap ℂ (fun i ↦ Lp ℂ (p i) μ) F)
    (C : ℝ)
    (hcore : ∀ x : ∀ i, aux_simpleFuncMemLpSubmodule (p i) μ,
      ‖B (fun i ↦ aux_simpleFuncMemLpToLp (p i) μ (x i))‖ ^ 2 ≤
        C * ∏ i, ‖aux_simpleFuncMemLpToLp (p i) μ (x i)‖ ^ 2) :
    ∀ g : ∀ i, Lp ℂ (p i) μ,
      ‖B g‖ ^ 2 ≤ C * ∏ i, ‖g i‖ ^ 2 := by
  apply aux_ContinuousMultilinearMap_norm_sq_le_of_denseRange_functions
    (E₀ := fun i ↦ aux_simpleFuncMemLpSubmodule (p i) μ)
    (B := B) (e := fun i ↦ aux_simpleFuncMemLpToLp (p i) μ) (C := C)
  · intro i
    exact aux_denseRange_simpleFuncMemLpToLp (p i) μ (hp_top i)
  · exact hcore
end Auto
