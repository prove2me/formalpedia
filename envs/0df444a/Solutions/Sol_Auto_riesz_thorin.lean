-- Prove2me | solution 1 for Auto.riesz_thorin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:12:48.853526+00:00
-- url     : https://prove2.me/submissions/c8525dcd-c6ec-4f15-aa8b-baf6d50eb758

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
public import Theorems.Thm_Auto_stein_interpolation_constant_bounds
section
@[expose] public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
namespace Auto
private theorem output_memLp_of_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p q : ENNReal} {M : ℝ}
    (T : SimpleFunc X ℂ → Y → ℂ)
    (hT_measurable : ∀ (f : SimpleFunc X ℂ),
      Integrable f μ → Measurable (T f))
    (hbound : ∀ (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T f) q ν ≤ ENNReal.ofReal M * eLpNorm (f : X → ℂ) p μ)
    (f : SimpleFunc X ℂ) (hf : Integrable f μ) :
    MemLp (T f) q ν := by
  have hfLp : MemLp (f : X → ℂ) p μ :=
    f.memLp_of_finite_measure_preimage p (SimpleFunc.integrable_iff.mp hf)
  refine ⟨(hT_measurable f hf).aestronglyMeasurable, ?_⟩
  exact (hbound f hf).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfLp.eLpNorm_lt_top)
private theorem pairing_integrable_of_endpoint_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p q : ENNReal} {M : ℝ}
    (hq : 1 ≤ q)
    (T : SimpleFunc X ℂ → Y → ℂ)
    (hT_measurable : ∀ (f : SimpleFunc X ℂ),
      Integrable f μ → Measurable (T f))
    (hbound : ∀ (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T f) q ν ≤ ENNReal.ofReal M * eLpNorm (f : X → ℂ) p μ) :
    ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable f μ → Integrable g ν → Integrable (fun y ↦ T f y * g y) ν := by
  intro f g hf hg
  let : Fact (1 ≤ q) := ⟨hq⟩
  have hTf : MemLp (T f) q ν := output_memLp_of_bound T hT_measurable hbound f hf
  have hgLp : MemLp (g : Y → ℂ) (ENNReal.conjExponent q) ν :=
    g.memLp_of_finite_measure_preimage _ (SimpleFunc.integrable_iff.mp hg)
  change Integrable (T f * (g : Y → ℂ)) ν
  exact hTf.integrable_mul hgLp
section
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
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    {p₀ p₁ p q₀ q₁ q : ENNReal} {θ M₀ M₁ : ℝ}
    (T : SimpleFunc X ℂ → Y → ℂ)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hθ : θ ∈ Set.Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (hT_add : ∀ (f g : SimpleFunc X ℂ),
      Integrable f μ → Integrable g μ → T (f + g) = T f + T g)
    (hT_smul : ∀ (c : ℂ) (f : SimpleFunc X ℂ),
      Integrable f μ → T (c • f) = c • T f)
    (hT_measurable : ∀ (f : SimpleFunc X ℂ),
      Integrable f μ → Measurable (T f))
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hbound₀ : ∀ (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T f) q₀ ν ≤ ENNReal.ofReal M₀ * eLpNorm (f : X → ℂ) p₀ μ)
    (hbound₁ : ∀ (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T f) q₁ ν ≤ ENNReal.ofReal M₁ * eLpNorm (f : X → ℂ) p₁ μ) :
    ∀ f : SimpleFunc X ℂ, Integrable f μ →
      MemLp (T f) q ν ∧
      eLpNorm (T f) q ν ≤
        ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) *
          eLpNorm (f : X → ℂ) p μ := by
  intro f hf
  refine stein_interpolation_constant_bounds (T := fun _ f ↦ T f)
    hp₀ hp₁ hq₀ hq₁ hθ hp hq ?_ ?_ ?_ ?_ ?_ ?_ hM₀ hM₁ ?_ ?_ f hf
  · intro z f g hf hg
    exact hT_add f g hf hg
  · intro z c f hf
    exact hT_smul c f hf
  · intro z f hf
    exact hT_measurable f hf
  · intro z f g hf hg
    exact pairing_integrable_of_endpoint_bound hq₀ T hT_measurable hbound₀ f g hf hg
  · intro f g hf hg
    exact diffContOnCl_const
  · refine ⟨0, Real.pi_pos, ?_⟩
    intro f g hf hg
    let N : ℝ := ‖∫ y, T f y * g y ∂ν‖
    refine ⟨N, ?_⟩
    intro z
    change N ≤ Real.exp (N * Real.exp (0 * |(z : ℂ).im|))
    calc
      N ≤ N + 1 := le_add_of_nonneg_right zero_le_one
      _ ≤ Real.exp N := add_one_le_exp _
      _ = Real.exp (N * Real.exp (0 * |(z : ℂ).im|)) := by simp
  · intro t f hf
    exact hbound₀ f hf
  · intro t f hf
    exact hbound₁ f hf
end Auto
