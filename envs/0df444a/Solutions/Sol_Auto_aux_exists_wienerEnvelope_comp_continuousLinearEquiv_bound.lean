-- Prove2me | solution 1 for Auto.aux_exists_wienerEnvelope_comp_continuousLinearEquiv_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:30.852195+00:00
-- url     : https://prove2.me/submissions/73fbde22-6124-4d1c-9eaa-52a9d377fee9

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_wienerEnvelope_comp_continuousLinearMap_le
public import Theorems.Thm_Auto_aux_integrable_comp_continuousLinearEquiv_between
public import Theorems.Thm_Auto_aux_integral_comp_continuousLinearEquiv_eq
public import Theorems.Thm_Auto_aux_exists_finite_closedBall_cover
public import Theorems.Thm_P2M_Auto_aux_integrable_wienerEnvelope_of_integrable__1e1fced5a7d3
public import Theorems.Thm_Auto_aux_integral_wienerEnvelope_le_card_mul_of_addHaar

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
    [NormedAddCommGroup K] (e : E ≃L[ℝ] F) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : F → K, MemW0 f →
      (∫ x, wienerEnvelope (f ∘ e) 1 x) ≤ C * ∫ y, wienerEnvelope f 1 y := by
  classical
  obtain ⟨t, ht⟩ :=
    aux_exists_finite_closedBall_cover (E := F) 1 zero_lt_one ‖(e : E →L[ℝ] F)‖
  let a : ℝ := (Measure.addHaarScalarFactor (Measure.map (e : E → F) volume) volume : ℝ)
  refine ⟨max 1 (a * (t.card : ℝ)),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro f hf
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hrad : Integrable (wienerEnvelope f ‖(e : E →L[ℝ] F)‖) :=
    aux_integrable_wienerEnvelope_of_integrable' hf.1 zero_lt_one (norm_nonneg _) hf.2
  have hrad_bound :
      (∫ y, wienerEnvelope f ‖(e : E →L[ℝ] F)‖ y) ≤
        (t.card : ℝ) * ∫ y, wienerEnvelope f 1 y :=
    aux_integral_wienerEnvelope_le_card_mul_of_addHaar hf.1 zero_lt_one (norm_nonneg _) hf.2 t ht
  have hcomp : Integrable (wienerEnvelope f ‖(e : E →L[ℝ] F)‖ ∘ e) :=
    aux_integrable_comp_continuousLinearEquiv_between hrad e
  have hleft : Integrable (wienerEnvelope (f ∘ e) 1) := by
    refine hcomp.mono_nonneg
      (continuous_wienerEnvelope (hf.1.comp e.continuous) 1).aestronglyMeasurable
      (ae_of_all _ fun x => aux_wienerEnvelope_nonneg (hf.1.comp e.continuous) zero_le_one x)
      (ae_of_all _ fun x => ?_)
    exact aux_wienerEnvelope_comp_continuousLinearMap_le e.toContinuousLinearMap hf.1 x
  have hmap : (∫ x, wienerEnvelope f ‖(e : E →L[ℝ] F)‖ (e x)) =
      a * ∫ y, wienerEnvelope f ‖(e : E →L[ℝ] F)‖ y := by
    simpa [a] using aux_integral_comp_continuousLinearEquiv_eq e
      (continuous_wienerEnvelope hf.1 ‖(e : E →L[ℝ] F)‖)
  have hnon : 0 ≤ ∫ y, wienerEnvelope f 1 y :=
    integral_nonneg fun y => aux_wienerEnvelope_nonneg hf.1 zero_le_one y
  calc
    (∫ x, wienerEnvelope (f ∘ e) 1 x) ≤
        ∫ x, wienerEnvelope f ‖(e : E →L[ℝ] F)‖ (e x) :=
      integral_mono hleft hcomp (fun x =>
        aux_wienerEnvelope_comp_continuousLinearMap_le e.toContinuousLinearMap hf.1 x)
    _ = a * ∫ y, wienerEnvelope f ‖(e : E →L[ℝ] F)‖ y := hmap
    _ ≤ a * ((t.card : ℝ) * ∫ y, wienerEnvelope f 1 y) :=
      mul_le_mul_of_nonneg_left hrad_bound ha
    _ = (a * (t.card : ℝ)) * ∫ y, wienerEnvelope f 1 y := by ring
    _ ≤ max 1 (a * (t.card : ℝ)) * ∫ y, wienerEnvelope f 1 y :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hnon
end Auto
