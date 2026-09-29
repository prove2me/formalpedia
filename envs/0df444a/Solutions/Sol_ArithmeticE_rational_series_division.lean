-- Prove2me | solution 1 for ArithmeticE.rational_series_division
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:58:58.420541+00:00
-- url     : https://prove2.me/submissions/a9ff3c24-5028-4e64-9992-4b4f277f8504

import Definitions.Def_rationalEArithmetic
import Theorems.Thm_ArithmeticE_rational_division_arithmetic
open scoped BigOperators
open ArithmeticE PowerSeries
namespace EulerEDivision
lemma division_series (a : ℕ → ℚ) (ha : RationalArithmetic a)
    (hz : HasSum (fun n : ℕ => (a n:ℝ)/(n.factorial:ℝ)) 0) :
    ∃ g : PowerSeries ℂ, RationalSeriesArithmetic g ∧
      (1-PowerSeries.X)*g = PowerSeries.mk (fun n => (a n:ℂ)/(n.factorial:ℂ)) := by
  let g : PowerSeries ℂ := PowerSeries.mk (fun n =>
    ∑ k ∈ Finset.range (n+1), (a k:ℂ)/(k.factorial:ℂ))
  refine ⟨g,?_,?_⟩
  · refine ⟨fun n => (n.factorial:ℚ)*∑ k ∈ Finset.range (n+1), a k/(k.factorial:ℚ),?_,ArithmeticE.rational_division_arithmetic a ha hz⟩
    intro n
    simp only [g,coeff_mk]
    push_cast
    rfl
  · apply PowerSeries.ext
    intro n
    rw [sub_mul,one_mul,map_sub]
    cases n with
    | zero => simp [g]
    | succ n =>
      simp only [coeff_succ_X_mul,g,coeff_mk,Finset.sum_range_succ]
      ring
end EulerEDivision

theorem solution (a : ℕ → ℚ) (ha : RationalArithmetic a)
    (hz : HasSum (fun n : ℕ => (a n:ℝ)/(n.factorial:ℝ)) 0) :
    ∃ g : PowerSeries ℂ, RationalSeriesArithmetic g ∧
      (1-PowerSeries.X)*g = PowerSeries.mk (fun n => (a n:ℂ)/(n.factorial:ℂ)) := by
  exact EulerEDivision.division_series a ha hz

#print axioms solution
