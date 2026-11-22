-- Prove2me | solution 1 for Auto.ae_snd_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:48:35.260101+00:00
-- url     : https://prove2.me/submissions/4e60e551-f817-441d-bdf8-bac5ecb147ee

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
theorem _root_.solution : ∀ᵐ p : ℝ × ℝ, p.2 ≠ 0 := by
  rw [Measure.volume_eq_prod]
  exact Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd
    (compl_mem_ae_iff.mpr (measure_singleton 0))
end Auto
