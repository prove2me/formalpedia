-- Prove2me | solution 1 for Auto.aux_norm_mul_unitClosedBallVolume_le_integral_wienerEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:50:58.83721+00:00
-- url     : https://prove2.me/submissions/ba81362e-bf30-4985-86ae-d18750bb3a9d

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_continuous
public import Theorems.Thm_Auto_MemW0_aux_integrable_envelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_norm_le_wienerEnvelope_of_mem_closedBall

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {d : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖f x‖ * volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      ∫ y, wienerEnvelope f 1 y := by
  let E := EuclideanSpace ℝ (Fin d)
  let s : Set E := closedBall x 1
  have hs : MeasurableSet s := measurableSet_closedBall
  have hs_fin : volume s ≠ ∞ := measure_closedBall_lt_top.ne
  have hbound : ∀ y ∈ s, ‖f x‖ ≤ wienerEnvelope f 1 y := by
    intro y hy
    apply aux_norm_le_wienerEnvelope_of_mem_closedBall hf.aux_continuous
    simpa [s, Metric.mem_closedBall, dist_comm] using hy
  have hset : ‖f x‖ * volume.real s ≤ ∫ y in s, wienerEnvelope f 1 y :=
    setIntegral_ge_of_const_le_real hs hs_fin hbound hf.aux_integrable_envelope.integrableOn
  calc
    ‖f x‖ * volume.real (closedBall (0 : E) 1) = ‖f x‖ * volume.real s := by
      rw [show volume.real s = volume.real (closedBall (0 : E) 1) by
        simpa [s] using MeasureTheory.Measure.addHaar_real_closedBall_center volume x 1]
    _ ≤ ∫ y in s, wienerEnvelope f 1 y := hset
    _ ≤ ∫ y, wienerEnvelope f 1 y :=
      setIntegral_le_integral hf.aux_integrable_envelope
        (ae_of_all _ fun y ↦ aux_wienerEnvelope_nonneg hf.aux_continuous zero_le_one y)
end Auto
