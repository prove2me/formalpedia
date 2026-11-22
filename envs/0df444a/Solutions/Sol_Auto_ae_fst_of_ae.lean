-- Prove2me | solution 1 for Auto.ae_fst_of_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:50:30.382636+00:00
-- url     : https://prove2.me/submissions/decb5aa0-0d8e-4924-9bf9-05993abda3ef

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
theorem _root_.solution {P : ℝ → Prop} (h : ∀ᵐ x, P x) : ∀ᵐ p : ℝ × ℝ, P p.1 := by
  rw [Measure.volume_eq_prod]
  exact Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h
end Auto
