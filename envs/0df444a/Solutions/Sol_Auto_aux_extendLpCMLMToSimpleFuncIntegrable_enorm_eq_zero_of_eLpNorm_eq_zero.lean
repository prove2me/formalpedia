-- Prove2me | solution 1 for Auto.aux_extendLpCMLMToSimpleFuncIntegrable_enorm_eq_zero_of_eLpNorm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:08.701167+00:00
-- url     : https://prove2.me/submissions/43d11aac-486f-4372-9381-c80abb61ca9f

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
section
@[expose] public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
namespace Auto
section
private theorem aux_extendLpCMLMToSimpleFuncIntegrable_eq_zero_of_eLpNorm_eq_zero
    {m : ℕ} {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : Fin (m + 1) → ENNReal) (μ : Measure X) [∀ i, Fact (1 ≤ p i)]
    (hp_top : ∀ i, p i ≠ ∞)
    (B : ContinuousMultilinearMap ℂ (fun i ↦ Lp ℂ (p i) μ) F)
    (u : Fin (m + 1) → ℝ) (hu : ∀ i, 0 < u i ∧ u i ≤ 1)
    (g : Fin (m + 1) → SimpleFunc X ℂ) (i : Fin (m + 1))
    (hzero : eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ = 0) :
    aux_extendLpCMLMToSimpleFuncIntegrable p μ hp_top B g = 0 := by
  have hqne : multilinearExponentOfReciprocal u i ≠ 0 := by
    unfold multilinearExponentOfReciprocal
    exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr (hu i).1)).ne'
  have hzero_ae : (g i : X → ℂ) =ᵐ[μ] 0 :=
    (eLpNorm_eq_zero_iff (g i).aestronglyMeasurable hqne).mp hzero
  have hgi_int : Integrable (g i : X → ℂ) μ :=
    (integrable_congr hzero_ae).mpr (integrable_zero X ℂ μ)
  have hgi_mem : MemLp (g i : X → ℂ) (p i) μ :=
    (SimpleFunc.memLp_iff_integrable
      (aux_simpleFuncExponent_ne_zero (p := p i)) (hp_top i)).mpr hgi_int
  have hinputzero :
      aux_integrableSimpleFuncToLp (p i) μ (hp_top i)
        (aux_integrableSimpleFuncRetract μ (g i)) = 0 := by
    rw [aux_integrableSimpleFuncRetract_apply_of_integrable μ (g i) hgi_int]
    rw [aux_integrableSimpleFuncToLp_apply (p i) μ (hp_top i) (g i) hgi_int]
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    exact (MemLp.coeFn_toLp hgi_mem).trans hzero_ae
  unfold aux_extendLpCMLMToSimpleFuncIntegrable
  exact B.toMultilinearMap.map_coord_zero i hinputzero
end
end Auto
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution
    {m : ℕ} {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : Fin (m + 1) → ENNReal) (μ : Measure X) [∀ i, Fact (1 ≤ p i)]
    (hp_top : ∀ i, p i ≠ ∞)
    (B : ContinuousMultilinearMap ℂ (fun i ↦ Lp ℂ (p i) μ) F)
    (u : Fin (m + 1) → ℝ) (hu : ∀ i, 0 < u i ∧ u i ≤ 1)
    (g : Fin (m + 1) → SimpleFunc X ℂ) (i : Fin (m + 1))
    (hzero : eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ = 0) :
    ‖aux_extendLpCMLMToSimpleFuncIntegrable p μ hp_top B g‖ₑ = 0 := by
  rw [aux_extendLpCMLMToSimpleFuncIntegrable_eq_zero_of_eLpNorm_eq_zero
    p μ hp_top B u hu g i hzero]
  simp
end Auto
