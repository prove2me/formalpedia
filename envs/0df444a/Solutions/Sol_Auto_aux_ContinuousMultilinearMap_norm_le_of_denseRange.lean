-- Prove2me | solution 1 for Auto.aux_ContinuousMultilinearMap_norm_le_of_denseRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:12.713379+00:00
-- url     : https://prove2.me/submissions/863428f2-ea2a-45dd-8585-262c4fe5dcd1

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
theorem _root_.solution
    {𝕜 ι F : Type*} {E₀ E : ι → Type*}
    [NontriviallyNormedField 𝕜] [Fintype ι]
    [∀ i, SeminormedAddCommGroup (E₀ i)] [∀ i, NormedSpace 𝕜 (E₀ i)]
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (B : ContinuousMultilinearMap 𝕜 E F)
    (e : ∀ i, E₀ i →L[𝕜] E i) (he : ∀ i, DenseRange (e i))
    (C : ℝ)
    (hbound : ∀ x : ∀ i, E₀ i,
      ‖B (fun i ↦ e i (x i))‖ ≤ C * ∏ i, ‖e i (x i)‖) :
    ∀ x : ∀ i, E i, ‖B x‖ ≤ C * ∏ i, ‖x i‖ := by
  let P : (∀ i, E i) → Prop := fun x ↦ ‖B x‖ ≤ C * ∏ i, ‖x i‖
  have hleft : Continuous fun x : ∀ i, E i ↦ ‖B x‖ := B.cont.norm
  have hprod : Continuous fun x : ∀ i, E i ↦ ∏ i, ‖x i‖ := by
    apply continuous_finsetProd Finset.univ
    intro i _
    exact continuous_norm.comp (continuous_apply i)
  have hright : Continuous fun x : ∀ i, E i ↦ C * ∏ i, ‖x i‖ :=
    continuous_const.mul hprod
  have hclosed : IsClosed {x : ∀ i, E i | P x} := by
    exact isClosed_le hleft hright
  intro x
  refine (DenseRange.piMap he).induction_on x hclosed ?_
  intro y
  exact hbound y
end Auto
