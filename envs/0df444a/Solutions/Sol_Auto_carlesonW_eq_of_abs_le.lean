-- Prove2me | solution 1 for Auto.carlesonW_eq_of_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:46:53.39481+00:00
-- url     : https://prove2.me/submissions/52d2d4df-553f-4016-88a3-cb39f8804c84

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_carlesonBump_eq_zero
public import Theorems.Thm_Auto_carlesonBump_eq_one

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution {t : ℝ} (ht : |t| ≤ 2) (u : ℝ) :
    carlesonW t u = carlesonBump₀ u := by
  unfold carlesonW
  by_cases hu : |u| < 2
  · rw [carlesonBump_eq_one carlesonBump₁ (x := 2 * u - t),
      carlesonBump_eq_one carlesonBump₁ (x := t - u), mul_one, mul_one]
    · change |t - u| ≤ 8
      rw [abs_le] at ht ⊢; rw [abs_lt] at hu; constructor <;> linarith
    · change |2 * u - t| ≤ 8
      rw [abs_le] at ht ⊢; rw [abs_lt] at hu; constructor <;> linarith
  · rw [carlesonBump_eq_zero carlesonBump₀ (not_lt.mp hu)]
    ring
end Auto
