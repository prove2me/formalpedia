-- Prove2me | solution 1 for Auto.aux_simpleFuncMemLpRetract_apply_of_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:53:36.850871+00:00
-- url     : https://prove2.me/submissions/d279e487-0e5e-460f-8cea-70f5168a8b8a

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
    aux_simpleFuncMemLpRetract p μ f =
      ⟨f, hf⟩ := by
  change (aux_simpleFuncMemLpSubmodule p μ).subtype.leftInverse
      ((aux_simpleFuncMemLpSubmodule p μ).subtype ⟨f, hf⟩) = ⟨f, hf⟩
  exact LinearMap.leftInverse_apply_of_inj
    (Submodule.ker_subtype (aux_simpleFuncMemLpSubmodule p μ)) ⟨f, hf⟩
end Auto
