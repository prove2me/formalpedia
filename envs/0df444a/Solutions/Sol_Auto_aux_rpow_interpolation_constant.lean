-- Prove2me | solution 1 for Auto.aux_rpow_interpolation_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:37.650793+00:00
-- url     : https://prove2.me/submissions/7e36a1f5-6909-4bed-9e67-55c6a44765ab

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
theorem _root_.solution {I V q : ℝ} (hI : 0 ≤ I) (hV : 0 < V)
    (hq : 1 ≤ q) :
    I ^ q⁻¹ * (I / V) ^ (1 - q⁻¹) = V ^ (q⁻¹ - 1) * I := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hqinv : 0 < q⁻¹ := inv_pos.mpr hq0
  by_cases hI0 : I = 0
  · simp [hI0, Real.zero_rpow hqinv.ne']
  · have hIpos : 0 < I := lt_of_le_of_ne hI (Ne.symm hI0)
    rw [Real.div_rpow hI hV.le]
    calc
      I ^ q⁻¹ * (I ^ (1 - q⁻¹) / V ^ (1 - q⁻¹)) =
          (I ^ q⁻¹ * I ^ (1 - q⁻¹)) / V ^ (1 - q⁻¹) := by ring
      _ = I ^ (q⁻¹ + (1 - q⁻¹)) / V ^ (1 - q⁻¹) := by
        rw [← Real.rpow_add hIpos]
      _ = I / V ^ (1 - q⁻¹) := by
        rw [show q⁻¹ + (1 - q⁻¹) = 1 by ring, Real.rpow_one]
      _ = V ^ (-(1 - q⁻¹)) * I := by
        rw [Real.rpow_neg hV.le]
        simp only [div_eq_mul_inv]
        ac_rfl
      _ = V ^ (q⁻¹ - 1) * I := by
        congr 2
        ring
end Auto
