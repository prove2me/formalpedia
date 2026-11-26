-- Prove2me | solution 1 for Auto.wienerNorm_le_max_one_three_mul_div_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:00:47.539722+00:00
-- url     : https://prove2.me/submissions/1b472fc2-f018-4eac-9e81-b2b40ccb5d37

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_integrable_wienerEnvelope_of_integrable
public import Theorems.Thm_Auto_aux_integral_wienerEnvelope_le_max_one_three_mul_div_pow_mul

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {d : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : Continuous f)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    wienerNorm f s ≤ ENNReal.ofReal (C_wienerNormRadiusIndependence d r s) * wienerNorm f r := by
  let C : ℝ := C_wienerNormRadiusIndependence d r s
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  by_cases htop : wienerNorm f r = ∞
  · change wienerNorm f s ≤ ENNReal.ofReal C * wienerNorm f r
    rw [htop]
    rw [ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCpos)]
    exact le_top
  · have hfr : Integrable (wienerEnvelope f r) :=
      (lintegral_ofReal_ne_top_iff_integrable
        (continuous_wienerEnvelope hf r).aestronglyMeasurable
        (ae_of_all _ fun x => aux_wienerEnvelope_nonneg hf (le_of_lt hr) x)).mp (by
          simpa [wienerNorm] using htop)
    have hfs : Integrable (wienerEnvelope f s) :=
      aux_integrable_wienerEnvelope_of_integrable hf hr (le_of_lt hs) hfr
    have hreal := aux_integral_wienerEnvelope_le_max_one_three_mul_div_pow_mul hf hr hs hfr
    have hwr : wienerNorm f r = ENNReal.ofReal (∫ x, wienerEnvelope f r x) := by
      unfold wienerNorm
      symm
      exact ofReal_integral_eq_lintegral_ofReal hfr
        (ae_of_all _ fun x => aux_wienerEnvelope_nonneg hf (le_of_lt hr) x)
    have hws : wienerNorm f s = ENNReal.ofReal (∫ x, wienerEnvelope f s x) := by
      unfold wienerNorm
      symm
      exact ofReal_integral_eq_lintegral_ofReal hfs
        (ae_of_all _ fun x => aux_wienerEnvelope_nonneg hf (le_of_lt hs) x)
    calc
      wienerNorm f s = ENNReal.ofReal (∫ x, wienerEnvelope f s x) := hws
      _ ≤ ENNReal.ofReal (C * ∫ x, wienerEnvelope f r x) :=
          ENNReal.ofReal_le_ofReal (by simpa [C, C_wienerNormRadiusIndependence] using hreal)
      _ = ENNReal.ofReal C * wienerNorm f r := by
        rw [ENNReal.ofReal_mul hCpos.le, ← hwr]
end Auto
