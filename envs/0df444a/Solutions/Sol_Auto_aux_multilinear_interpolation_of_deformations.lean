-- Prove2me | solution 1 for Auto.aux_multilinear_interpolation_of_deformations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:09:41.148455+00:00
-- url     : https://prove2.me/submissions/48149c89-3dd8-4914-8d93-d1706290c1a5

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
    (hp₀ : ∀ i, 1 ≤ p₀ i) (hp₁ : ∀ i, 1 ≤ p₁ i) (hq : 1 ≤ q)
    (hint : (p 0)⁻¹ = ENNReal.ofReal (1 - θ) * (p₀ 0)⁻¹ +
      ENNReal.ofReal θ * (p₁ 0)⁻¹)
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
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
    (hg₀ : Integrable (g₀ : X → ℂ) μ)
    (D : ℂ → Fin m → SimpleFunc X ℂ)
    (hD_theta : ∀ i, D (θ : ℂ) i = g i)
    (hD_integrable : ∀ (z : verticalClosedStrip 0 1) i,
      Integrable (D z i : X → ℂ) μ)
    (hD_left : ∀ (t : ℝ) i,
      eLpNorm (D ((t : ℂ) * Complex.I) i : X → ℂ) (p₀ i.succ) μ ≤ 1)
    (hD_right : ∀ (t : ℝ) i,
      eLpNorm (D (1 + (t : ℂ) * Complex.I) i : X → ℂ) (p₁ i.succ) μ ≤ 1)
    (hB_analytic : ∀ (f : SimpleFunc X ℂ) (g' : SimpleFunc Y ℂ),
      Integrable (f : X → ℂ) μ → Integrable (g' : Y → ℂ) ν →
      DiffContOnCl ℂ (fun z ↦ ∫ y, B f (D z) y * g' y ∂ν) (verticalStrip 0 1))
    (hB_growth : ∃ a : ℝ, a < Real.pi ∧
      ∀ (f : SimpleFunc X ℂ) (g' : SimpleFunc Y ℂ),
        Integrable (f : X → ℂ) μ → Integrable (g' : Y → ℂ) ν →
        ∃ C : ℝ, ∀ z : verticalClosedStrip 0 1,
          ‖∫ y, B f (D z) y * g' y ∂ν‖ ≤
            Real.exp (C * Real.exp (a * |(z : ℂ).im|))) :
    MemLp (B g₀ g) q ν ∧
      eLpNorm (B g₀ g) q ν ≤
        ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) *
          eLpNorm (g₀ : X → ℂ) (p 0) μ := by
  let T : ℂ → SimpleFunc X ℂ → Y → ℂ := fun z f ↦ B f (D z)
  have hweight : ENNReal.ofReal (1 - θ) + ENNReal.ofReal θ = 1 := by
    rw [← ENNReal.ofReal_add (by linarith [hθ.2]) hθ.1.le]
    norm_num
  have hqint : q⁻¹ = ENNReal.ofReal (1 - θ) * q⁻¹ + ENNReal.ofReal θ * q⁻¹ := by
    rw [← add_mul, hweight, one_mul]
  have hT_add : ∀ (z : verticalClosedStrip 0 1) (f k : SimpleFunc X ℂ),
      Integrable (f : X → ℂ) μ → Integrable (k : X → ℂ) μ →
        T z (f + k) = T z f + T z k := by
    intro z f k hf hk
    exact hB_add f k (D z) hf hk
  have hT_smul : ∀ (z : verticalClosedStrip 0 1) (c : ℂ) (f : SimpleFunc X ℂ),
      Integrable (f : X → ℂ) μ → T z (c • f) = c • T z f := by
    intro z c f hf
    exact hB_smul c f (D z) hf
  have hT_measurable : ∀ (z : verticalClosedStrip 0 1) (f : SimpleFunc X ℂ),
      Integrable (f : X → ℂ) μ → Measurable (T z f) := by
    intro z f hf
    exact hB_measurable f (D z) hf (hD_integrable z)
  have hT_pair_integrable : ∀ (z : verticalClosedStrip 0 1)
      (f : SimpleFunc X ℂ) (g' : SimpleFunc Y ℂ),
      Integrable (f : X → ℂ) μ → Integrable (g' : Y → ℂ) ν →
        Integrable (fun y ↦ T z f y * g' y) ν := by
    intro z f g' hf hg'
    exact hB_pair_integrable f (D z) g' hf (hD_integrable z) hg'
  have hT_analytic : ∀ (f : SimpleFunc X ℂ) (g' : SimpleFunc Y ℂ),
      Integrable (f : X → ℂ) μ → Integrable (g' : Y → ℂ) ν →
      DiffContOnCl ℂ (fun z ↦ ∫ y, T z f y * g' y ∂ν) (verticalStrip 0 1) := by
    intro f g' hf hg'
    exact hB_analytic f g' hf hg'
  have hT_growth : ∃ a : ℝ, a < Real.pi ∧
      ∀ (f : SimpleFunc X ℂ) (g' : SimpleFunc Y ℂ),
        Integrable (f : X → ℂ) μ → Integrable (g' : Y → ℂ) ν →
        ∃ C : ℝ, ∀ z : verticalClosedStrip 0 1,
          ‖∫ y, T z f y * g' y ∂ν‖ ≤
            Real.exp (C * Real.exp (a * |(z : ℂ).im|)) := hB_growth
  have hT_bound₀ : ∀ (t : ℝ) (f : SimpleFunc X ℂ), Integrable (f : X → ℂ) μ →
      eLpNorm (T ((t : ℂ) * Complex.I) f) q ν ≤
        ENNReal.ofReal M₀ * eLpNorm (f : X → ℂ) (p₀ 0) μ := by
    intro t f hf
    have hprod : ∏ i, eLpNorm (D ((t : ℂ) * Complex.I) i : X → ℂ) (p₀ i.succ) μ ≤ 1 := by
      exact Finset.prod_le_one (fun _ _ ↦ bot_le) (fun i _ ↦ hD_left t i)
    calc
      eLpNorm (T ((t : ℂ) * Complex.I) f) q ν ≤
          ENNReal.ofReal M₀ * eLpNorm (f : X → ℂ) (p₀ 0) μ *
            ∏ i, eLpNorm (D ((t : ℂ) * Complex.I) i : X → ℂ) (p₀ i.succ) μ :=
        hB_bound₀ f (D ((t : ℂ) * Complex.I)) hf
          (hD_integrable ⟨_, by simp [verticalClosedStrip]⟩)
      _ ≤ ENNReal.ofReal M₀ * eLpNorm (f : X → ℂ) (p₀ 0) μ * 1 := by gcongr
      _ = ENNReal.ofReal M₀ * eLpNorm (f : X → ℂ) (p₀ 0) μ := by rw [mul_one]
  have hT_bound₁ : ∀ (t : ℝ) (f : SimpleFunc X ℂ), Integrable (f : X → ℂ) μ →
      eLpNorm (T (1 + (t : ℂ) * Complex.I) f) q ν ≤
        ENNReal.ofReal M₁ * eLpNorm (f : X → ℂ) (p₁ 0) μ := by
    intro t f hf
    have hprod : ∏ i, eLpNorm (D (1 + (t : ℂ) * Complex.I) i : X → ℂ) (p₁ i.succ) μ ≤ 1 := by
      exact Finset.prod_le_one (fun _ _ ↦ bot_le) (fun i _ ↦ hD_right t i)
    calc
      eLpNorm (T (1 + (t : ℂ) * Complex.I) f) q ν ≤
          ENNReal.ofReal M₁ * eLpNorm (f : X → ℂ) (p₁ 0) μ *
            ∏ i, eLpNorm (D (1 + (t : ℂ) * Complex.I) i : X → ℂ) (p₁ i.succ) μ :=
        hB_bound₁ f (D (1 + (t : ℂ) * Complex.I)) hf
          (hD_integrable ⟨_, by simp [verticalClosedStrip]⟩)
      _ ≤ ENNReal.ofReal M₁ * eLpNorm (f : X → ℂ) (p₁ 0) μ * 1 := by gcongr
      _ = ENNReal.ofReal M₁ * eLpNorm (f : X → ℂ) (p₁ 0) μ := by rw [mul_one]
  obtain ⟨hmem, hnorm⟩ := stein_interpolation_constant_bounds T
    (hp₀ 0) (hp₁ 0) hq hq hθ hint hqint hT_add hT_smul hT_measurable
      hT_pair_integrable hT_analytic hT_growth hM₀ hM₁ hT_bound₀ hT_bound₁ g₀ hg₀
  have hT_theta : T (θ : ℂ) g₀ = B g₀ g := by
    dsimp only [T]
    rw [show D (θ : ℂ) = g by funext i; exact hD_theta i]
  rw [hT_theta] at hmem hnorm
  exact ⟨hmem, hnorm⟩
end Auto
