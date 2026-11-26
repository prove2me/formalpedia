-- Prove2me | solution 1 for Auto.aux_integrable_wienerEnvelope_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:53:00.155374+00:00
-- url     : https://prove2.me/submissions/b0130318-4f02-48e3-925c-e6daa72dc7eb

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {E F 𝕜 : Type*} [NormedAddCommGroup E]
    [ProperSpace E] [MeasureSpace E] [BorelSpace E] [SFinite (volume : Measure E)]
    [NormedAddCommGroup F] [ProperSpace F] [MeasureSpace F] [BorelSpace F]
    [SFinite (volume : Measure F)]
    [NormedField 𝕜] {f : E → 𝕜} {g : F → 𝕜} (hf : Continuous f) (hg : Continuous g)
    (hfi : Integrable (wienerEnvelope f 1)) (hgi : Integrable (wienerEnvelope g 1)) :
    Integrable (fun x : E × F ↦ wienerEnvelope f 1 x.1 * wienerEnvelope g 1 x.2) := by
  rw [Measure.volume_eq_prod]
  let h : E × F → ℝ := fun x ↦ wienerEnvelope f 1 x.1 * wienerEnvelope g 1 x.2
  have hh : AEStronglyMeasurable h (volume.prod volume) := by
    change AEStronglyMeasurable (fun x : E × F ↦
      wienerEnvelope f 1 x.1 * wienerEnvelope g 1 x.2) (volume.prod volume)
    exact ((continuous_wienerEnvelope hf 1).comp continuous_fst).mul
      ((continuous_wienerEnvelope hg 1).comp continuous_snd) |>.aestronglyMeasurable
  refine (integrable_prod_iff hh).mpr ⟨?_, ?_⟩
  · filter_upwards [] with x
    exact hgi.const_mul (wienerEnvelope f 1 x)
  · have hformula : ∀ x : E,
        (∫ y, ‖wienerEnvelope f 1 x * wienerEnvelope g 1 y‖) =
          wienerEnvelope f 1 x * ∫ y, wienerEnvelope g 1 y := by
      intro x
      calc
        (∫ y, ‖wienerEnvelope f 1 x * wienerEnvelope g 1 y‖) =
            ∫ y, wienerEnvelope f 1 x * wienerEnvelope g 1 y := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (aux_wienerEnvelope_nonneg hf zero_le_one _)
              (aux_wienerEnvelope_nonneg hg zero_le_one _))]
        _ = wienerEnvelope f 1 x * ∫ y, wienerEnvelope g 1 y :=
          integral_const_mul _ _
    change Integrable (fun x : E ↦
      ∫ y, ‖wienerEnvelope f 1 x * wienerEnvelope g 1 y‖) volume
    convert hfi.mul_const (∫ y, wienerEnvelope g 1 y) using 1
    ext x
    exact hformula x
end Auto
