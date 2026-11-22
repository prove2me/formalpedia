-- Prove2me | solution 1 for Auto.carlesonW_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:44:41.912186+00:00
-- url     : https://prove2.me/submissions/64605c47-2faa-4a8d-8f94-d1c358371028

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_carlesonBump_eq_zero

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution {t : ℝ} (ht : 11 ≤ |t|) (u : ℝ) : carlesonW t u = 0 := by
  unfold carlesonW
  by_cases hu : |u| < 2
  · rw [carlesonBump_eq_zero carlesonBump₁ (x := t - u), mul_zero]
    change (9 : ℝ) ≤ |t - u|
    have := abs_sub_abs_le_abs_sub t u
    linarith
  · rw [carlesonBump_eq_zero carlesonBump₀ (not_lt.mp hu)]
    ring
end Auto
