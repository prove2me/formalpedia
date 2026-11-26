-- Prove2me | solution 1 for Auto.aux_eLpNorm_sq_packLpContinuousLinearMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:08:04.14779+00:00
-- url     : https://prove2.me/submissions/41a6e7d5-4346-4f7e-9b76-6cc4b8fb89f4

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

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SFinite μ]
    (u : PiLp 2 (fun _ : Fin J ↦ Lp ℂ 2 μ)) :
    eLpNorm ((aux_packLpContinuousLinearMap (μ := μ) u :
      Lp ℂ 2 ((Measure.count : Measure (Fin J)).prod μ)) : Fin J × X → ℂ) 2
        ((Measure.count : Measure (Fin J)).prod μ) ^ 2 =
      ∑ j : Fin J, eLpNorm (u j : X → ℂ) 2 μ ^ 2 := by
  change eLpNorm ((aux_packLpLinearMap (μ := μ)) (fun j ↦ u j) : Fin J × X → ℂ) 2
      ((Measure.count : Measure (Fin J)).prod μ) ^ 2 = _
  exact aux_eLpNorm_sq_packLpLinearMap (fun j ↦ u j)
end Auto
