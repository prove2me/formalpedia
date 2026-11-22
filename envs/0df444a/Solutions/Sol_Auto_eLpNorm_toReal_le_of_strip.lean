-- Prove2me | solution 1 for Auto.eLpNorm_toReal_le_of_strip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:48:50.080033+00:00
-- url     : https://prove2.me/submissions/b1d94943-c664-4f25-bca2-63b2ee9a98e8

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution {f : ℝ × ℝ → ℂ} {a : ℝ → ℝ} {r c : ℝ} (hr : 0 ≤ r)
    (ha : Measurable a) (ha₃ : Integrable fun x => |a x| ^ 3)
    (hf : ∀ p, ‖f p‖ ≤ |a p.1|) (hz : ∀ p, r < |p.2 + c * p.1| → f p = 0) :
    (eLpNorm f 3 volume).toReal ≤ (2 * r * ∫ x, |a x| ^ 3) ^ (1 / 3 : ℝ) := by
  set S := {p : ℝ × ℝ | |p.2 + c * p.1| ≤ r}
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hpt : ∀ p, ‖f p‖ₑ ^ (3 : ℝ) ≤ S.indicator (fun p => ‖a p.1‖ₑ ^ (3 : ℝ)) p := by
    intro p
    by_cases hp : p ∈ S
    · rw [indicator_of_mem hp]
      gcongr
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((hf p).trans_eq (Real.norm_eq_abs _).symm)
    · rw [hz p (lt_of_not_ge hp)]
      simp
  have hsec : ∀ x : ℝ, volume {y : ℝ | |y + c * x| ≤ r} = ENNReal.ofReal (2 * r) := by
    intro x
    have : {y : ℝ | |y + c * x| ≤ r} = Icc (-r - c * x) (r - c * x) := by
      ext y
      simp only [mem_ofPred_eq, mem_Icc, abs_le]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [this, Real.volume_Icc]
    ring_nf
  have hlin : ∫⁻ p, ‖f p‖ₑ ^ (3 : ℝ) ≤ ENNReal.ofReal (2 * r) * ∫⁻ x, ‖a x‖ₑ ^ (3 : ℝ) := by
    calc ∫⁻ p, ‖f p‖ₑ ^ (3 : ℝ) ≤ ∫⁻ p, S.indicator (fun p => ‖a p.1‖ₑ ^ (3 : ℝ)) p :=
          lintegral_mono hpt
      _ = ∫⁻ x, ‖a x‖ₑ ^ (3 : ℝ) * ENNReal.ofReal (2 * r) := by
          rw [Measure.volume_eq_prod, lintegral_prod _
            ((Measurable.indicator (by fun_prop) hS).aemeasurable)]
          congr 1
          ext x
          have : (fun y => S.indicator (fun p : ℝ × ℝ => ‖a p.1‖ₑ ^ (3 : ℝ)) (x, y)) =
              {y : ℝ | |y + c * x| ≤ r}.indicator fun _ => ‖a x‖ₑ ^ (3 : ℝ) := by
            ext y
            by_cases hy : |y + c * x| ≤ r <;> simp [S, indicator, hy]
          rw [this, lintegral_indicator_const (measurableSet_le (by fun_prop) measurable_const),
            hsec]
      _ = ENNReal.ofReal (2 * r) * ∫⁻ x, ‖a x‖ₑ ^ (3 : ℝ) := by
          rw [lintegral_mul_const _ (by fun_prop), mul_comm]
  have hI : ∫⁻ x, ‖a x‖ₑ ^ (3 : ℝ) = ENNReal.ofReal (∫ x, |a x| ^ 3) := by
    rw [ofReal_integral_eq_lintegral_ofReal ha₃ (ae_of_all _ fun x => by positivity)]
    congr 1
    ext x
    rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _)
      (by norm_num)]
    norm_num
  have hnn : 0 ≤ ∫ x, |a x| ^ 3 := integral_nonneg fun x => by positivity
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h3 : (3 : ℝ≥0∞).toReal = 3 := by norm_num
  rw [h3, ← ENNReal.toReal_rpow]
  gcongr
  rw [hI, ← ENNReal.ofReal_mul (by positivity)] at hlin
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin
end Auto
