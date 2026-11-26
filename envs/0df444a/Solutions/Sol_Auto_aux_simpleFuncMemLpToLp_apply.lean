-- Prove2me | solution 1 for Auto.aux_simpleFuncMemLpToLp_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:12:53.101726+00:00
-- url     : https://prove2.me/submissions/0880461d-5579-4ef6-ac36-82bd66a4f4a8

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
    (p : ℝ≥0∞) (μ : Measure X) (f : SimpleFunc X ℂ)
    (hf : MemLp (f : X → ℂ) p μ) :
    aux_simpleFuncMemLpToLp p μ ⟨f, hf⟩ = hf.toLp f :=
  rfl
end Auto
