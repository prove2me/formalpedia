-- Prove2me | solution 1 for Auto.aux_packLpCMLM_coeFn_ae_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:47.691665+00:00
-- url     : https://prove2.me/submissions/c03c9040-343a-43ae-bdf5-6bc0e19f492d

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
public import Theorems.Thm_Auto_aux_packLpContinuousLinearMap_coeFn_ae_of_forall
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
    ((aux_packLpCMLM B x : Lp ℂ 2 ((Measure.count : Measure (Fin J)).prod μ)) :
      Fin J × Y → ℂ) =ᵐ[(Measure.count : Measure (Fin J)).prod μ]
      fun z ↦ raw z.1 z.2 := by
  rw [aux_packLpCMLM_apply]
  apply aux_packLpContinuousLinearMap_coeFn_ae_of_forall
  intro j
  simpa using hraw j
end Auto
