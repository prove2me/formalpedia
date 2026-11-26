-- Prove2me | solution 1 for Auto.aux_extendLpCMLMToSimpleFuncIntegrable_apply_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:12:59.380881+00:00
-- url     : https://prove2.me/submissions/57dc1b37-5169-453e-9b0d-952ffc0751b7

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
public import Theorems.Thm_Auto_aux_integrableSimpleFuncRetract_apply_of_integrable
public import Theorems.Thm_Auto_aux_integrableSimpleFuncToLp_apply

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution {ι X F : Type*}
    [Fintype ι] [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : ι → ENNReal) (μ : Measure X) [∀ i, Fact (1 ≤ p i)]
    (hp_top : ∀ i, p i ≠ ∞)
    (B : ContinuousMultilinearMap ℂ (fun i ↦ Lp ℂ (p i) μ) F)
    (f : ∀ _i, SimpleFunc X ℂ)
    (hf : ∀ i, Integrable (f i : X → ℂ) μ) :
    aux_extendLpCMLMToSimpleFuncIntegrable p μ hp_top B f =
      B fun i ↦ ((SimpleFunc.memLp_iff_integrable
        (aux_simpleFuncExponent_ne_zero (p := p i)) (hp_top i)).mpr
        (hf i)).toLp (f i) := by
  change B.toMultilinearMap (fun i ↦
    aux_integrableSimpleFuncToLp (p i) μ (hp_top i)
      (aux_integrableSimpleFuncRetract μ (f i))) =
    B.toMultilinearMap (fun i ↦
      ((SimpleFunc.memLp_iff_integrable
        (aux_simpleFuncExponent_ne_zero (p := p i)) (hp_top i)).mpr
        (hf i)).toLp (f i))
  congr 1
  funext i
  rw [aux_integrableSimpleFuncRetract_apply_of_integrable μ (f i) (hf i)]
  exact aux_integrableSimpleFuncToLp_apply (p i) μ (hp_top i) (f i) (hf i)
end Auto
