-- Prove2me | solution 1 for Auto.carlesonMoll_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:49:53.426138+00:00
-- url     : https://prove2.me/submissions/eb9e3011-74e7-4920-8db5-bef691dcfb60

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Auto
theorem _root_.solution (k : ℕ) {h : ℝ → E} {A : ℝ} (hh : ∀ x, A < |x| → h x = 0) {x : ℝ}
    (hx : A + 1 < |x|) : carlesonMoll k h x = 0 := by
  by_contra hne
  obtain ⟨s, hs, y, hy, rfl⟩ := support_convolution_subset _ (Function.mem_support.mpr hne)
  rw [(carlesonMollifier k).support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hs
  have hs' : |s| < 1 := hs.trans_le (by
    change 2 / ((k : ℝ) + 2) ≤ 1
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hy' : |y| ≤ A := not_lt.mp fun h' => hy (hh y h')
  linarith [abs_add_le s y]
end Auto
