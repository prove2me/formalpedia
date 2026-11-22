-- Prove2me | solution 1 for Auto.triangular_kernel_pairing_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:49:43.359499+00:00
-- url     : https://prove2.me/submissions/3ad3f45e-d6b6-4578-b34f-60163b04afa8

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_continuous_Kern
public import Theorems.Thm_Auto_triangular_Kern_mul_bound
public import Theorems.Thm_Auto_triangular_Kern_mul_tendsto

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
theorem _root_.solution {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : X → ℂ} {r : X → ℝ} (hg : Integrable g μ) (hr : Measurable r) (hz : ∀ᵐ x ∂μ, r x ≠ 0) :
    Tendsto (fun n : ℕ => ∫ x, g x * ((r x * Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) (r x) : ℝ) :
      ℂ) ∂μ) atTop (𝓝 ((triangularKernelCoefficient : ℂ) * ∫ x, g x ∂μ)) := by
  have hp : ∀ n : ℕ, 0 < ((n : ℝ) + 1)⁻¹ := fun n => by positivity
  have hab : ∀ n : ℕ, ((n : ℝ) + 1)⁻¹ ≤ (n : ℝ) + 1 := by
    intro n
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    exact ((inv_le_one₀ hn0).mpr hn1).trans hn1
  have hlim : Tendsto (fun n : ℕ => ∫ x, g x *
      ((r x * Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) (r x) : ℝ) : ℂ) ∂μ)
      atTop (𝓝 (∫ x, g x * (triangularKernelCoefficient : ℂ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => (6 * triangularKernelCoefficient) * ‖g x‖)
    · intro n
      have hm : Measurable (fun x =>
          ((r x * Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) (r x) : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp
          (hr.mul ((continuous_Kern 3 (hp n) (hab n)).measurable.comp hr))
      exact hg.aestronglyMeasurable.mul hm.aestronglyMeasurable
    · exact hg.norm.const_mul _
    · intro n
      filter_upwards [] with x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h := triangular_Kern_mul_bound (hp n) (hab n) (r x)
      nlinarith [mul_le_mul_of_nonneg_left h (norm_nonneg (g x))]
    · filter_upwards [hz] with x hx
      exact tendsto_const_nhds.mul
        (Complex.continuous_ofReal.continuousAt.tendsto.comp (triangular_Kern_mul_tendsto hx))
  simpa [integral_mul_const, mul_comm] using hlim
end Auto
