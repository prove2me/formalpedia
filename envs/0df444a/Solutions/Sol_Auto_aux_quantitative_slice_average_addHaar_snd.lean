-- Prove2me | solution 1 for Auto.aux_quantitative_slice_average_addHaar_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:38.141821+00:00
-- url     : https://prove2.me/submissions/c1eac389-c268-4205-99bc-83fcf888c5e6

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [SFinite (volume : Measure E)]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [SFinite (volume : Measure F)]
    [Measure.IsAddHaarMeasure (volume : Measure F)]
    {H : E × F → ℝ} {G : E → ℝ} (hH : Integrable H (volume.prod volume))
    (hHnonneg : ∀ p, 0 ≤ H p) (hG : Continuous G) (hGnonneg : ∀ u, 0 ≤ G u)
    (v : F) (hpoint : ∀ v' ∈ closedBall v 1, ∀ u, G u ≤ H (u, v')) :
    (volume : Measure F).real (closedBall 0 1) * ∫ u, G u ≤ ∫ p, H p ∂(volume.prod volume) := by
  let A : Set F := closedBall v 1
  let I : E × F → ℝ := (Set.univ ×ˢ A).indicator (fun p => G p.1)
  have hA : MeasurableSet A := measurableSet_closedBall
  have hIAE : AEStronglyMeasurable I (volume.prod volume) := by
    exact ((hG.comp continuous_fst).stronglyMeasurable.aestronglyMeasurable)
      |>.indicator (MeasurableSet.univ.prod hA)
  have hIpoint (p : E × F) : ‖I p‖ ≤ H p := by
    by_cases hp : p.2 ∈ A
    · rw [show I p = G p.1 by simp [I, hp]]
      simpa [Real.norm_eq_abs, abs_of_nonneg (hGnonneg p.1)] using hpoint p.2 hp p.1
    · rw [show I p = 0 by simp [I, hp]]
      simpa using hHnonneg p
  have hI : Integrable I (volume.prod volume) := hH.mono' hIAE (ae_of_all _ hIpoint)
  have hIleH : I ≤ H := by
    intro p
    by_cases hp : p.2 ∈ A
    · rw [show I p = G p.1 by simp [I, hp]]
      exact hpoint p.2 hp p.1
    · rw [show I p = 0 by simp [I, hp]]
      exact hHnonneg p
  have hinter (v' : F) :
      (∫ u, I (u, v')) = A.indicator (fun _ => ∫ u, G u) v' := by
    by_cases hv : v' ∈ A <;> simp [I, hv]
  have hmain : (volume : Measure F).real A * ∫ u, G u ≤ ∫ p, H p ∂(volume.prod volume) := by
    calc
      (volume : Measure F).real A * ∫ u, G u = ∫ v' in A, ∫ u, G u := by
        rw [setIntegral_const, smul_eq_mul]
      _ = ∫ v', A.indicator (fun _ => ∫ u, G u) v' := (integral_indicator hA).symm
      _ = ∫ v', ∫ u, I (u, v') := by
        apply integral_congr_ae
        filter_upwards [] with v'
        rw [hinter v']
      _ = ∫ p, I p ∂(volume.prod volume) := (integral_prod_symm _ hI).symm
      _ ≤ ∫ p, H p ∂(volume.prod volume) := integral_mono hI hH hIleH
  have htrans : MeasurePreserving (fun x : F => x + v) (volume : Measure F) volume :=
    measurePreserving_add_right volume v
  have hpreimage : (fun x : F => x + v) ⁻¹' A = closedBall 0 1 := by
    ext x
    change dist (x + v) v ≤ 1 ↔ dist x 0 ≤ 1
    simp [dist_eq_norm]
  have hmeasure : (volume : Measure F) A = (volume : Measure F) (closedBall (0 : F) 1) := by
    calc
      (volume : Measure F) A = (volume : Measure F) ((fun x : F => x + v) ⁻¹' A) :=
        (htrans.measure_preimage hA.nullMeasurableSet).symm
      _ = (volume : Measure F) (closedBall 0 1) := congrArg volume hpreimage
  have hmeasure_real : (volume : Measure F).real A =
      (volume : Measure F).real (closedBall (0 : F) 1) := by
    simp only [measureReal_def, hmeasure]
  rw [hmeasure_real] at hmain
  exact hmain
end Auto
