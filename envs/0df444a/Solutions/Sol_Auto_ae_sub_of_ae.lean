-- Prove2me | solution 1 for Auto.ae_sub_of_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:51:12.062489+00:00
-- url     : https://prove2.me/submissions/80dc761f-52dd-47d0-974e-3806f5338280

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
namespace Auto
theorem _root_.solution {P : ℝ → Prop} (h : ∀ᵐ x, P x) : ∀ᵐ p : ℝ × ℝ, P (p.1 - p.2) := by
  rw [Measure.volume_eq_prod]
  exact Measure.QuasiMeasurePreserving.ae (quasiMeasurePreserving_sub_of_right_invariant volume volume) h
end Auto
