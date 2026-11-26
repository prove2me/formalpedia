-- Prove2me | solution 1 for Auto.aux_eLpNorm_sq_packLpCMLM_eq_sum_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:48.60763+00:00
-- url     : https://prove2.me/submissions/66277a42-4949-4fb2-9e75-ec1c9b052b24

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
public import Theorems.Thm_Auto_aux_eLpNorm_sq_packLpContinuousLinearMap_eq_sum_raw
public import Theorems.Thm_Auto_aux_packLpCMLM_apply
attribute [local simp] Auto.aux_packLpCMLM_apply

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution {J : ℕ} {ι Y : Type*} {X : ι → Type*}
    [Fintype ι] [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]
    [∀ i, SeminormedAddCommGroup (X i)] [∀ i, NormedSpace ℂ (X i)]
    (B : Fin J → ContinuousMultilinearMap ℂ X (Lp ℂ 2 μ)) (x : ∀ i, X i)
    (raw : Fin J → Y → ℂ) (hraw : ∀ j, (B j x : Y → ℂ) =ᵐ[μ] raw j) :
    eLpNorm ((aux_packLpCMLM B x : Lp ℂ 2 ((Measure.count : Measure (Fin J)).prod μ)) :
      Fin J × Y → ℂ) 2 ((Measure.count : Measure (Fin J)).prod μ) ^ 2 =
      ∑ j : Fin J, eLpNorm (raw j) 2 μ ^ 2 := by
  rw [aux_packLpCMLM_apply]
  apply aux_eLpNorm_sq_packLpContinuousLinearMap_eq_sum_raw
  intro j
  simpa using hraw j
end Auto
