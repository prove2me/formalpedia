-- Prove2me | solution 1 for Auto.aux_denseRange_simpleFuncMemLpToLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:07:21.164292+00:00
-- url     : https://prove2.me/submissions/0da3265b-61d6-43a4-9751-afcbb7805e04

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
    (p : ℝ≥0∞) (μ : Measure X) [Fact (1 ≤ p)] (hp_top : p ≠ ∞) :
    DenseRange (aux_simpleFuncMemLpToLp p μ) := by
  change Dense (Set.range (aux_simpleFuncMemLpToLp p μ))
  apply Dense.mono ?_ (Lp.simpleFunc.denseRange (E := ℂ) (μ := μ) hp_top)
  rintro f ⟨g, rfl⟩
  refine ⟨⟨Lp.simpleFunc.toSimpleFunc g, Lp.simpleFunc.memLp g⟩, ?_⟩
  change (Lp.simpleFunc.memLp g).toLp (Lp.simpleFunc.toSimpleFunc g) = (g : Lp ℂ p μ)
  rw [← Lp.simpleFunc.toLp_eq_toLp]
  exact congrArg Subtype.val (Lp.simpleFunc.toLp_toSimpleFunc g)
end Auto
