-- Prove2me | solution 1 for Auto.aux_eLpNorm_interpolation_one_top_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:32.114576+00:00
-- url     : https://prove2.me/submissions/c5291d92-9614-4fca-b14e-af73b568f7d1

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution
    {E 𝕜 : Type*} [MeasurableSpace E] [NormedAddCommGroup 𝕜] {μ : Measure E}
    {f : E → 𝕜} (hf : AEStronglyMeasurable f μ) {q : ℝ} (hq : 1 < q) :
    eLpNorm f (ENNReal.ofReal q) μ ≤
      (eLpNorm f 1 μ) ^ q⁻¹ * (eLpNorm f ∞ μ) ^ (1 - q⁻¹) := by
  let a : E → ℝ := fun x ↦ ‖f x‖
  let b : E → ℝ := fun x ↦ ‖f x‖ ^ (q - 1)
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hqsub : 0 < q - 1 := sub_pos.mpr hq
  have ha : AEStronglyMeasurable a μ := hf.norm
  have hmul :
      eLpNorm (fun x ↦ a x * b x) 1 μ ≤
        (1 : ℝ≥0∞) * eLpNorm a 1 μ * eLpNorm b ∞ μ := by
    apply eLpNorm_le_eLpNorm_mul_eLpNorm_top 1 ha b (· * ·) 1
    filter_upwards with x
    simp
  have hab : (fun x ↦ a x * b x) = fun x ↦ ‖f x‖ ^ q := by
    funext x
    dsimp [a, b]
    by_cases hx : ‖f x‖ = 0
    · simp [hx, Real.zero_rpow hq0.ne']
    · have hfx : f x ≠ 0 := by
        intro hfx
        apply hx
        simp [hfx]
      have hpos : 0 < (‖f x‖ : ℝ) := norm_pos_iff.mpr hfx
      calc
        ‖f x‖ * ‖f x‖ ^ (q - 1) = ‖f x‖ ^ (1 : ℝ) * ‖f x‖ ^ (q - 1) := by
          rw [Real.rpow_one]
        _ = ‖f x‖ ^ ((1 : ℝ) + (q - 1)) :=
          (@Real.rpow_add ‖f x‖ hpos 1 (q - 1)).symm
        _ = ‖f x‖ ^ q := by
          congr 1
          ring
  have hpow : eLpNorm f (ENNReal.ofReal q) μ ^ q ≤
      eLpNorm f 1 μ * eLpNorm f ∞ μ ^ (q - 1) := by
    have hqsub0 : ENNReal.ofReal (q - 1) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hqsub)
    calc
      eLpNorm f (ENNReal.ofReal q) μ ^ q =
          eLpNorm (fun x ↦ ‖f x‖ ^ q) 1 μ := by
        symm
        simpa using (eLpNorm_norm_rpow (p := (1 : ℝ≥0∞)) f hq0)
      _ = eLpNorm (fun x ↦ a x * b x) 1 μ := by rw [hab]
      _ ≤ (1 : ℝ≥0∞) * eLpNorm a 1 μ * eLpNorm b ∞ μ := hmul
      _ = eLpNorm f 1 μ * eLpNorm f ∞ μ ^ (q - 1) := by
        rw [show a = fun x ↦ ‖f x‖ by rfl, eLpNorm_norm]
        rw [show b = fun x ↦ ‖f x‖ ^ (q - 1) by rfl,
          eLpNorm_norm_rpow f hqsub]
        rw [ENNReal.top_mul hqsub0, eLpNorm_exponent_top]
        simp
  have hpow' := ENNReal.rpow_le_rpow hpow (inv_nonneg.mpr hq0.le)
  rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hq0.ne', ENNReal.rpow_one] at hpow'
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hq0.le), ← ENNReal.rpow_mul] at hpow'
  convert hpow' using 1
  congr 3
  field_simp
end Auto
