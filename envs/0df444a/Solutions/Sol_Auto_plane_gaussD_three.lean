-- Prove2me | solution 1 for Auto.plane_gaussD_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:33:16.057856+00:00
-- url     : https://prove2.me/submissions/6f333f86-e951-44c7-ba1b-b3a18d1b0c15

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_abs_gaussianD_le_const
public import Theorems.Thm_Auto_gaussianD_conv_gaussianD
public import Theorems.Thm_Auto_integrable_fin2_prod

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution (d₀ d₁ d₂ : ℕ) {σ : ℝ} (hσ : 0 < σ) (c₀ c₁ c₂ : ℝ) :
    Integrable (fun q : Fin 2 → ℝ => ((gaussianD d₀ σ (c₀ - q 0) * gaussianD d₁ σ (c₁ - q 1) *
      gaussianD d₂ σ (c₂ + q 0 + q 1) : ℝ) : ℂ)) ∧ ∫ q : Fin 2 → ℝ, ((gaussianD d₀ σ (c₀ - q 0) *
      gaussianD d₁ σ (c₁ - q 1) * gaussianD d₂ σ (c₂ + q 0 + q 1) : ℝ) : ℂ) = (gaussianD (d₂ + d₁
      + d₀) (σ + σ + σ) (c₀ + c₁ + c₂) : ℂ) := by
  obtain ⟨M, hM⟩ := abs_gaussianD_le_const d₂ hσ
  have h0 : Integrable (fun x => gaussianD d₀ σ (c₀ - x)) :=
    (integrable_gaussianD d₀ hσ).comp_sub_left c₀
  have h1 : Integrable (fun x => gaussianD d₁ σ (c₁ - x)) :=
    (integrable_gaussianD d₁ hσ).comp_sub_left c₁
  have hcont : Continuous (fun q : Fin 2 → ℝ => gaussianD d₀ σ (c₀ - q 0) *
      gaussianD d₁ σ (c₁ - q 1) * gaussianD d₂ σ (c₂ + q 0 + q 1)) := by
    have := continuous_gaussianD d₀ σ
    have := continuous_gaussianD d₁ σ
    have := continuous_gaussianD d₂ σ
    fun_prop
  have hI : Integrable (fun q : Fin 2 → ℝ => gaussianD d₀ σ (c₀ - q 0) *
      gaussianD d₁ σ (c₁ - q 1) * gaussianD d₂ σ (c₂ + q 0 + q 1)) := by
    refine ((integrable_fin2_prod h0 h1).norm.const_mul M).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, abs_mul]
    have := hM (c₂ + q 0 + q 1)
    have := abs_nonneg (gaussianD d₀ σ (c₀ - q 0))
    have := abs_nonneg (gaussianD d₁ σ (c₁ - q 1))
    nlinarith [mul_nonneg (abs_nonneg (gaussianD d₀ σ (c₀ - q 0)))
      (abs_nonneg (gaussianD d₁ σ (c₁ - q 1)))]
  refine ⟨hI.ofReal, ?_⟩
  rw [integral_complex_ofReal]
  congr 1
  have hfin : ∫ q : Fin 2 → ℝ, gaussianD d₀ σ (c₀ - q 0) * gaussianD d₁ σ (c₁ - q 1) *
      gaussianD d₂ σ (c₂ + q 0 + q 1) = ∫ x, ∫ y, gaussianD d₀ σ (c₀ - x) *
        gaussianD d₁ σ (c₁ - y) * gaussianD d₂ σ (c₂ + x + y) := by
    have h2 := (volume_preserving_finTwoArrow ℝ).symm
    rw [← h2.integral_comp' (g := fun q : Fin 2 → ℝ => gaussianD d₀ σ (c₀ - q 0) *
      gaussianD d₁ σ (c₁ - q 1) * gaussianD d₂ σ (c₂ + q 0 + q 1)), Measure.volume_eq_prod,
      integral_prod]
    · rfl
    · exact (h2.integrable_comp_emb MeasurableEquiv.finTwoArrow.symm.measurableEmbedding).2 hI
  rw [hfin]
  have inner : ∀ x, ∫ y, gaussianD d₀ σ (c₀ - x) * gaussianD d₁ σ (c₁ - y) *
      gaussianD d₂ σ (c₂ + x + y) =
      gaussianD d₀ σ (c₀ - x) * gaussianD (d₂ + d₁) (σ + σ) (c₂ + x + c₁) := by
    intro x
    rw [← gaussianD_conv_gaussianD d₂ d₁ hσ hσ, ← integral_const_mul]
    rw [← integral_sub_left_eq_self (fun d => gaussianD d₀ σ (c₀ - x) *
      (gaussianD d₂ σ (c₂ + x + c₁ - d) * gaussianD d₁ σ d)) volume c₁]
    congr 1; funext y
    rw [show c₂ + x + c₁ - (c₁ - y) = c₂ + x + y by ring]; ring
  simp_rw [inner]
  rw [← gaussianD_conv_gaussianD (d₂ + d₁) d₀ (by positivity : 0 < σ + σ) hσ,
    ← integral_sub_left_eq_self (fun d => gaussianD (d₂ + d₁) (σ + σ) (c₀ + c₁ + c₂ - d) *
      gaussianD d₀ σ d) volume c₀]
  congr 1; funext x
  rw [show c₀ + c₁ + c₂ - (c₀ - x) = c₂ + x + c₁ by ring]; ring
end Auto
