-- Prove2me | solution 1 for Auto.aux_wienerNormOne_mul_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:53:19.604047+00:00
-- url     : https://prove2.me/submissions/1e044cc5-c089-4433-b8ec-fa44e746c79a

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_measurable_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_wienerEnvelope_mul_prod_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {E F 𝕜 : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [NormedAddCommGroup F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [SFinite (volume : Measure F)] [NormedField 𝕜]
    {f : E → 𝕜} {g : F → 𝕜}
    (hf : Continuous f) (hg : Continuous g) :
    wienerNormOne (fun x : E × F ↦ f x.1 * g x.2) ≤ wienerNormOne f * wienerNormOne g := by
  unfold wienerNormOne wienerNorm
  rw [Measure.volume_eq_prod]
  calc
    (∫⁻ x : E × F, ENNReal.ofReal (wienerEnvelope (fun x : E × F ↦ f x.1 * g x.2) 1 x)) ≤
        ∫⁻ x : E × F, ENNReal.ofReal
          (wienerEnvelope f 1 x.1 * wienerEnvelope g 1 x.2) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal (aux_wienerEnvelope_mul_prod_le hf hg x)
    _ = (∫⁻ x : E, ENNReal.ofReal (wienerEnvelope f 1 x)) *
        ∫⁻ y : F, ENNReal.ofReal (wienerEnvelope g 1 y) := by
      simp_rw [ENNReal.ofReal_mul (aux_wienerEnvelope_nonneg hf zero_le_one _)]
      exact lintegral_prod_mul
        (f := fun x : E ↦ ENNReal.ofReal (wienerEnvelope f 1 x))
        (g := fun y : F ↦ ENNReal.ofReal (wienerEnvelope g 1 y))
        (ENNReal.continuous_ofReal.measurable.comp_aemeasurable
          (measurable_wienerEnvelope hf 1).aemeasurable)
        (ENNReal.continuous_ofReal.measurable.comp_aemeasurable
          (measurable_wienerEnvelope hg 1).aemeasurable)
end Auto
