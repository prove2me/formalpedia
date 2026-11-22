-- Prove2me | solution 1 for Auto.triangularHilbert_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:59:24.319241+00:00
-- url     : https://prove2.me/submissions/8337e4ea-1cba-437b-a572-315dd35ef33e

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_sourceGaussian_bound
public import Theorems.Thm_Auto_triangularKernelCoefficient_pos
public import Theorems.Thm_Auto_triangular_scale_tendsto
public import Theorems.Thm_Auto_sourceGaussian_schwartz_integrable
public import Theorems.Thm_Auto_sourceGaussian_integral_eq

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
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) :
    ‖triangularHilbert F₀ F₁ F₂‖ ≤ triangularBoundConstant *
      (eLpNorm F₀ 3).toReal * (eLpNorm F₁ 3).toReal * (eLpNorm F₂ 3).toReal := by
  let F : Fin 3 → SchwartzMap (ℝ × ℝ) ℂ := ![F₀, F₁, F₂]
  have hlim : Tendsto
      (fun n : ℕ => ∫ x, sourceGaussianIntegrand (fun v => F v)
        ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) x) atTop
      (𝓝 ((triangularKernelCoefficient : ℂ) * triangularHilbert F₀ F₁ F₂)) := by
    convert (triangular_scale_tendsto F₀ (triangularPullback₁ F₁)
      (triangularPullback₂ F₂)).neg using 1
    · ext n
      exact sourceGaussian_integral_eq F (by positivity) (by
        have h : (1 : ℝ) ≤ n + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
        exact ((inv_le_one₀ (by positivity)).mpr h).trans h)
    · simp [triangularHilbert]
  have hb : ‖(triangularKernelCoefficient : ℂ) * triangularHilbert F₀ F₁ F₂‖ ≤
      3 * heatBoundConstant *
        (eLpNorm F₀ 3).toReal * (eLpNorm F₁ 3).toReal * (eLpNorm F₂ 3).toReal := by
    apply le_of_tendsto' hlim.norm
    intro n
    have ha : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
    have hab : ((n : ℝ) + 1)⁻¹ ≤ (n : ℝ) + 1 := by
      have h : (1 : ℝ) ≤ n + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
      exact ((inv_le_one₀ (by positivity)).mpr h).trans h
    have h := sourceGaussian_bound (fun v => F v) (fun v => (F v).continuous)
      (fun v => (F v).memLp 3) ha hab (sourceGaussian_schwartz_integrable F ha hab)
    simpa [F, Fin.prod_univ_succ, mul_assoc] using h
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos triangularKernelCoefficient_pos] at hb
  have hd := (le_div_iff₀ triangularKernelCoefficient_pos).mpr
    (show ‖triangularHilbert F₀ F₁ F₂‖ * triangularKernelCoefficient ≤
      3 * heatBoundConstant *
        (eLpNorm F₀ 3).toReal * (eLpNorm F₁ 3).toReal * (eLpNorm F₂ 3).toReal from by
      simpa only [mul_comm] using hb)
  convert hd using 1 <;> first | rfl | (unfold triangularBoundConstant; ring)
end Auto
