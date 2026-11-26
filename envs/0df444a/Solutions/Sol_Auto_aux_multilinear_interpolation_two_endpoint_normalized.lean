-- Prove2me | solution 1 for Auto.aux_multilinear_interpolation_two_endpoint_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:11:04.772378+00:00
-- url     : https://prove2.me/submissions/8f68ca2a-4ea6-408f-a3da-4500e322fc83

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
public import Theorems.Thm_Auto_aux_multilinear_input_deformation_properties
public import Theorems.Thm_Auto_aux_multilinear_interpolation_of_deformations

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution
    {m : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    (B : SimpleFunc X ℂ → (Fin m → SimpleFunc X ℂ) → Y → ℂ)
    {p₀ p₁ p : Fin (m + 1) → ENNReal} {q : ENNReal} {θ M₀ M₁ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hp₀ : ∀ i, 1 ≤ p₀ i) (hp₁ : ∀ i, 1 ≤ p₁ i) (hp : ∀ i, 1 ≤ p i)
    (hp_top : ∀ i, p i ≠ ∞)
    (hint : ∀ i, (p i)⁻¹ = ENNReal.ofReal (1 - θ) * (p₀ i)⁻¹ +
      ENNReal.ofReal θ * (p₁ i)⁻¹)
    (hq : 1 ≤ q) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hB_add : ∀ (f g : SimpleFunc X ℂ) (u : Fin m → SimpleFunc X ℂ),
      Integrable (f : X → ℂ) μ → Integrable (g : X → ℂ) μ →
        B (f + g) u = B f u + B g u)
    (hB_smul : ∀ (c : ℂ) (f : SimpleFunc X ℂ) (u : Fin m → SimpleFunc X ℂ),
      Integrable (f : X → ℂ) μ → B (c • f) u = c • B f u)
    (hB_measurable : ∀ (f : SimpleFunc X ℂ) (u : Fin m → SimpleFunc X ℂ),
      Integrable (f : X → ℂ) μ → (∀ i, Integrable (u i : X → ℂ) μ) →
        Measurable (B f u))
    (hB_pair_integrable : ∀ (f : SimpleFunc X ℂ) (u : Fin m → SimpleFunc X ℂ)
      (g : SimpleFunc Y ℂ), Integrable (f : X → ℂ) μ →
      (∀ i, Integrable (u i : X → ℂ) μ) → Integrable (g : Y → ℂ) ν →
        Integrable (fun y ↦ B f u y * g y) ν)
    (hB_bound₀ : ∀ (f : SimpleFunc X ℂ) (u : Fin m → SimpleFunc X ℂ),
      Integrable (f : X → ℂ) μ → (∀ i, Integrable (u i : X → ℂ) μ) →
      eLpNorm (B f u) q ν ≤ ENNReal.ofReal M₀ * eLpNorm (f : X → ℂ) (p₀ 0) μ *
        ∏ i, eLpNorm (u i : X → ℂ) (p₀ i.succ) μ)
    (hB_bound₁ : ∀ (f : SimpleFunc X ℂ) (u : Fin m → SimpleFunc X ℂ),
      Integrable (f : X → ℂ) μ → (∀ i, Integrable (u i : X → ℂ) μ) →
      eLpNorm (B f u) q ν ≤ ENNReal.ofReal M₁ * eLpNorm (f : X → ℂ) (p₁ 0) μ *
        ∏ i, eLpNorm (u i : X → ℂ) (p₁ i.succ) μ)
    (g₀ : SimpleFunc X ℂ) (g : Fin m → SimpleFunc X ℂ)
    (hg₀ : Integrable (g₀ : X → ℂ) μ) (hg : ∀ i, Integrable (g i : X → ℂ) μ)
    (hgnorm : ∀ i, eLpNorm (g i : X → ℂ) (p i.succ) μ ≤ 1)
    (hB_analytic : ∀ (f : SimpleFunc X ℂ) (g' : SimpleFunc Y ℂ),
      Integrable (f : X → ℂ) μ → Integrable (g' : Y → ℂ) ν →
      DiffContOnCl ℂ (fun z ↦ ∫ y,
        B f (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p g z i) y * g' y ∂ν)
        (verticalStrip 0 1))
    (hB_growth : ∃ a : ℝ, a < Real.pi ∧
      ∀ (f : SimpleFunc X ℂ) (g' : SimpleFunc Y ℂ),
        Integrable (f : X → ℂ) μ → Integrable (g' : Y → ℂ) ν →
        ∃ C : ℝ, ∀ z : verticalClosedStrip 0 1,
          ‖∫ y, B f (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p g z i) y * g' y ∂ν‖ ≤
            Real.exp (C * Real.exp (a * |(z : ℂ).im|))) :
    MemLp (B g₀ g) q ν ∧
      eLpNorm (B g₀ g) q ν ≤
        ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) *
          eLpNorm (g₀ : X → ℂ) (p 0) μ := by
  obtain ⟨hD_theta, hD_integrable, hD_left, hD_right⟩ :=
    aux_multilinear_input_deformation_properties hθ hp₀ hp₁ hp hp_top hint g hg hgnorm
  exact aux_multilinear_interpolation_of_deformations B hθ hp₀ hp₁ hq (hint 0)
    hM₀ hM₁ hB_add hB_smul hB_measurable hB_pair_integrable hB_bound₀ hB_bound₁
    g₀ g hg₀ (aux_multilinear_input_deformation p₀ p₁ p g)
    hD_theta hD_integrable hD_left hD_right hB_analytic hB_growth
end Auto
