-- Prove2me | solution 1 for Auto.aux_integrableSimpleFuncRetract_apply_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:23.959832+00:00
-- url     : https://prove2.me/submissions/0d7e305f-00eb-4d94-bce5-9d6f99003187

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
theorem _root_.solution {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : SimpleFunc X ℂ) (hf : Integrable (f : X → ℂ) μ) :
    aux_integrableSimpleFuncRetract μ f = ⟨f, (memLp_one_iff_integrable.mpr hf)⟩ := by
  exact aux_simpleFuncMemLpRetract_apply_of_memLp 1 μ f (memLp_one_iff_integrable.mpr hf)
end Auto
