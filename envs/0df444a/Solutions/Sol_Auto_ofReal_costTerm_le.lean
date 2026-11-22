-- Prove2me | solution 1 for Auto.ofReal_costTerm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:05:46.074836+00:00
-- url     : https://prove2.me/submissions/e32edc1d-93e9-4b20-aa56-eef172dfee00

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [Fintype m] [DecidableEq m]
namespace Auto
theorem _root_.solution (k x : ℂ) {c : ℝ} (hc : 0 ≤ c) :
    ENNReal.ofReal ((3 / 2) * (2 * ((starRingEnd ℂ) k * x).re - c * ‖x‖ ^ 2)) ≤ ENNReal.ofReal
      ((3 / 2) * ‖k‖ ^ 2) / ENNReal.ofReal c := by
  rcases hc.eq_or_lt with rfl | hc
  · by_cases hk : k = 0
    · subst hk; simp
    · rw [ENNReal.ofReal_zero, ENNReal.div_zero (by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)]
      exact le_top
  · rw [← ENNReal.ofReal_div_of_pos hc]
    apply ENNReal.ofReal_le_ofReal
    have h1 : ((starRingEnd ℂ) k * x).re ≤ ‖k‖ * ‖x‖ := by
      refine (Complex.re_le_norm _).trans ?_
      simp
    rw [le_div_iff₀ hc]
    nlinarith [sq_nonneg (‖k‖ - c * ‖x‖), norm_nonneg k, norm_nonneg x]
end Auto
