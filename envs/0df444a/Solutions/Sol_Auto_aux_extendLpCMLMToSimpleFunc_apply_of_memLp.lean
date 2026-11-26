-- Prove2me | solution 1 for Auto.aux_extendLpCMLMToSimpleFunc_apply_of_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:12:56.428977+00:00
-- url     : https://prove2.me/submissions/029ceef0-2dd5-456b-b965-f23ecc363ae0

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
public import Theorems.Thm_Auto_aux_simpleFuncMemLpRetract_apply_of_memLp

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
    (p : ι → ℝ≥0∞) (μ : Measure X) [∀ i, Fact (1 ≤ p i)]
    (B : ContinuousMultilinearMap ℂ (fun i ↦ Lp ℂ (p i) μ) F)
    (f : ∀ _i : ι, SimpleFunc X ℂ)
    (hf : ∀ i, MemLp (f i : X → ℂ) (p i) μ) :
    aux_extendLpCMLMToSimpleFunc p μ B f =
      B fun i ↦ (hf i).toLp (f i) := by
  change B.toMultilinearMap (fun i ↦
    aux_simpleFuncMemLpToLp (p i) μ
      (aux_simpleFuncMemLpRetract (p i) μ (f i))) =
    B.toMultilinearMap (fun i ↦ (hf i).toLp (f i))
  congr 1
  funext i
  rw [aux_simpleFuncMemLpRetract_apply_of_memLp (p i) μ (f i) (hf i)]
  rfl
end Auto
