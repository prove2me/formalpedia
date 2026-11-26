-- Prove2me | solution 1 for Auto.aux_denseRange_integrableSimpleFuncToLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:09.20798+00:00
-- url     : https://prove2.me/submissions/c9abf08d-8ce5-4d40-ae0f-31b0fb9c5f96

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
public import Theorems.Thm_Auto_aux_integrableSimpleFuncToLp_apply

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution {X : Type*} [MeasurableSpace X]
    (p : ENNReal) (μ : Measure X) [Fact (1 ≤ p)] (hp_top : p ≠ ∞) :
    DenseRange (aux_integrableSimpleFuncToLp p μ hp_top) := by
  change Dense (Set.range (aux_integrableSimpleFuncToLp p μ hp_top))
  apply Dense.mono ?_ (Lp.simpleFunc.denseRange (E := ℂ) (μ := μ) hp_top)
  rintro f ⟨g, rfl⟩
  have hg_int : Integrable (Lp.simpleFunc.toSimpleFunc g : X → ℂ) μ :=
    (SimpleFunc.memLp_iff_integrable
      (aux_simpleFuncExponent_ne_zero (p := p)) hp_top).mp
      (Lp.simpleFunc.memLp g)
  refine ⟨⟨Lp.simpleFunc.toSimpleFunc g, memLp_one_iff_integrable.mpr hg_int⟩, ?_⟩
  rw [aux_integrableSimpleFuncToLp_apply p μ hp_top (Lp.simpleFunc.toSimpleFunc g) hg_int]
  change (Lp.simpleFunc.memLp g).toLp (Lp.simpleFunc.toSimpleFunc g) = (g : Lp ℂ p μ)
  rw [← Lp.simpleFunc.toLp_eq_toLp]
  exact congrArg Subtype.val (Lp.simpleFunc.toLp_toSimpleFunc g)
end Auto
