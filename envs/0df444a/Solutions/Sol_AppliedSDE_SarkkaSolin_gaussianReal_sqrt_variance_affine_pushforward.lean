-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussianReal_sqrt_variance_affine_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:11:10.289328+00:00
-- url     : https://prove2.me/submissions/6f537997-30c9-420c-af74-757a22aded57

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (b q y h : ℝ) (hq : 0 < q) (hh : 0 ≤ h) :
    (gaussianReal 0 1).map
      (fun z : ℝ => Real.sqrt (q * h) * z + (y + b * h)) =
    gaussianReal (y + b * h) (q * h).toNNReal := by
  have hqh : 0 ≤ q * h := mul_nonneg hq.le hh
  let c : ℝ := Real.sqrt (q * h)
  let v : ℝ≥0 := ⟨c ^ 2, sq_nonneg c⟩
  have hv : v = (q * h).toNNReal := by
    rw [Real.toNNReal_of_nonneg hqh]
    apply Subtype.ext
    exact Real.sq_sqrt hqh
  have hm : (gaussianReal 0 1).map (fun z : ℝ => c * z) =
      gaussianReal 0 (q * h).toNNReal := by
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one]
    exact congrArg (gaussianReal 0) hv
  calc
    (gaussianReal 0 1).map
        (fun z : ℝ => c * z + (y + b * h)) =
      ((gaussianReal 0 1).map (fun z : ℝ => c * z)).map
        (fun z : ℝ => z + (y + b * h)) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
    _ = (gaussianReal 0 (q * h).toNNReal).map
        (fun z : ℝ => z + (y + b * h)) := by rw [hm]
    _ = gaussianReal (y + b * h) (q * h).toNNReal := by
          rw [gaussianReal_map_add_const]
          simp only [zero_add]
