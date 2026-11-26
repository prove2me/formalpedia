-- Prove2me | solution 1 for Auto.aux_integrableSimpleFuncToLp_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:46:06.627038+00:00
-- url     : https://prove2.me/submissions/f7c22cb4-88d5-4a40-813c-62b81a4ff718

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
theorem _root_.solution {X : Type*} [MeasurableSpace X]
    (p : ENNReal) (μ : Measure X) [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    (f : SimpleFunc X ℂ) (hf : Integrable (f : X → ℂ) μ) :
    aux_integrableSimpleFuncToLp p μ hp_top ⟨f, memLp_one_iff_integrable.mpr hf⟩ =
      ((SimpleFunc.memLp_iff_integrable
        (aux_simpleFuncExponent_ne_zero (p := p)) hp_top).mpr hf).toLp f := by
  rfl
end Auto
