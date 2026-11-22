-- Prove2me | solution 1 for Auto.gaussian_conv_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:39:27.535016+00:00
-- url     : https://prove2.me/submissions/9fea5937-3457-4b80-8514-911b8e13bac0

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal symmDiff
noncomputable section
open Real
namespace Auto
theorem _root_.solution {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (t : ℝ) :
    ∫ d, gaussian σ (t - d) * gaussian τ d = gaussian (σ + τ) t := by
  set b := (σ + τ) / (2 * σ * τ) with hb
  have hb0 : 0 < b := by positivity
  set c := τ / (σ + τ)
  have hsq : ∀ d : ℝ, gaussian σ (t - d) * gaussian τ d = ((√(2 * π * σ))⁻¹ * (√(2 * π * τ))⁻¹ *
      Real.exp (-(t ^ 2) / (2 * (σ + τ)))) *
        Real.exp (-b * (d - c * t) ^ 2) := by
    intro d
    unfold gaussian
    have : Real.exp (-((t - d) ^ 2) / (2 * σ)) * Real.exp (-(d ^ 2) / (2 * τ)) =
        Real.exp (-(t ^ 2) / (2 * (σ + τ))) * Real.exp (-b * (d - c * t) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [hb, c]
      field_simp
      ring
    calc
      _ = (√(2 * π * σ))⁻¹ * (√(2 * π * τ))⁻¹ *
          (Real.exp (-((t - d) ^ 2) / (2 * σ)) * Real.exp (-(d ^ 2) / (2 * τ))) := by ring
      _ = _ := by rw [this]; ring
  simp_rw [hsq]
  rw [integral_const_mul]
  have hshift : ∫ d : ℝ, Real.exp (-b * (d - c * t) ^ 2) = √(π / b) := by
    rw [integral_sub_right_eq_self (fun d => Real.exp (-b * d ^ 2)) (c * t), integral_gaussian]
  rw [hshift]
  unfold gaussian
  rw [show ∀ x y z w : ℝ, x * y * z * w = (x * y * w) * z by intros; ring]
  congr 1
  rw [← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity),
    ← Real.sqrt_mul (by positivity)]
  congr 1
  simp only [hb]
  field_simp
end Auto
