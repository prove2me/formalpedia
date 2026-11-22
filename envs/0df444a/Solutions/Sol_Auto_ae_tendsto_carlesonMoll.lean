-- Prove2me | solution 1 for Auto.ae_tendsto_carlesonMoll
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:50:00.571199+00:00
-- url     : https://prove2.me/submissions/03aadabb-61e1-410c-8036-affceabe4c14

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
theorem _root_.solution [CompleteSpace E] {h : ℝ → E} (hh : LocallyIntegrable h) :
    ∀ᵐ x, Tendsto (fun k => carlesonMoll k h x) atTop (𝓝 (h x)) := by
  refine ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := carlesonMollifier) (K := 2) ?_ (Eventually.of_forall fun k => ?_) hh
  · change Tendsto (fun k : ℕ => 2 / ((k : ℝ) + 2)) atTop (𝓝 0)
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  · change 2 / ((k : ℝ) + 2) ≤ 2 * (1 / ((k : ℝ) + 2))
    rw [mul_one_div]
end Auto
