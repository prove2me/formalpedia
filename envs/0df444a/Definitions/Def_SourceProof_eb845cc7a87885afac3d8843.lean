-- Prove2me | Definitions.Def_SourceProof_eb845cc7a87885afac3d8843
-- name    : SourceProof_eb845cc7a87885afac3d8843
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:38:21.071446+00:00
-- url     : https://prove2.me/theorems/2ac9c7d9-5023-4ba2-a802-5264f475eb49
-- title:
--   LevyStochCalc source module: SourceProof_eb845cc7a87885afac3d8843
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.exists_sBoundedProcess_picardStep` comes from the `LevyStochCalc.Ito.PicardOutputModification` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F001
import Definitions.Def_SourceProof_146d3b4e1dccf65e2e9025d2
import Definitions.Def_SourceProof_1720d71b3049591278c59d6d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Càdlàg modifications of the Picard step

The `L²` stochastic integral is defined separately at each time, so the Picard step as first
written has no path regularity. Replacing each Brownian component by a càdlàg adapted
modification, and the drift by its almost surely continuous version, produces a process
indistinguishable from the step at every fixed time and càdlàg along almost every path; the
Bielecki norm is unchanged, and the result is a genuine self-map of the space of bounded
adapted càdlàg processes.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

section Modification

variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (X : ℝ → Ω → (Fin n → ℝ))
variable (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
  Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
variable (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
  Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
variable (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (x₀ : Fin n → ℝ)
variable (h_γ_meas : ∀ i : Fin n,
  Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
variable (h_γ_progMeas : ∀ i : Fin n,
  Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
variable (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)


theorem _root_.Prove2MeSourceProof.h_eb845cc7a87885afac3d8843 [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (h_μ_progMeas : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.μ s (X s ω) i))
    (h_μ_sq : ∀ i : Fin n, ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ}
    (hμT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hσT : ∀ i : Fin n, ∀ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∃ Y : SBoundedProcess (n := n) P ℱ T, ∀ t : ℝ,
      Y.X t =ᵐ[P] picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t := by
  classical
  have hrc : ℱ.rightCont = ℱ := MeasureTheory.Filtration.IsRightContinuous.eq
  have hadapt : ∀ (i : Fin n) (t : ℝ), Measurable[ℱ t] fun ω =>
      LevyStochCalc.Ito.Picard.picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq t ω i := by
    intro i t
    have h := LevyStochCalc.Ito.Picard.picardStepMod_adapted W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
      h_γ_meas h_γ_progMeas h_γ_sq h_μ_progMeas i t
    rwa [hrc] at h
  have hex : ∀ i : Fin n, ∃ Z : ℝ → Ω → ℝ, (∀ t : ℝ, Measurable[ℱ t] (Z t)) ∧
      (∀ t : ℝ, Z t =ᵐ[P] fun ω =>
        LevyStochCalc.Ito.Picard.picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
          h_γ_meas h_γ_progMeas h_γ_sq t ω i) ∧
      (∀ (ω : Ω) (t : ℝ),
        Filter.Tendsto (fun s => Z s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Z t ω))) ∧
      ∀ (ω : Ω) (t : ℝ), ∃ L : ℝ,
        Filter.Tendsto (fun s => Z s ω) (nhdsWithin t (Set.Iio t)) (nhds L) := fun i =>
    _root_.Prove2MeSourceProof.h_1720d71b3049591278c59d6d hℱ0 hnull (hadapt i)
      (LevyStochCalc.Ito.Picard.picardStepMod_cadlag W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq h_μ_meas h_μ_sq i)
  choose Z hZmeas hZae hZright hZleft using hex
  have hstepae : ∀ t : ℝ, (fun ω i => Z i t ω) =ᵐ[P]
      LevyStochCalc.Ito.Picard.picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq t := by
    intro t
    filter_upwards [MeasureTheory.ae_all_iff.mpr fun i : Fin n => hZae i t] with ω hω
    exact funext fun i => hω i
  refine ⟨{
    X := fun t ω i => Z i t ω
    measurable_path := measurable_pi_lambda _ fun i =>
      LevyStochCalc.Probability.measurable_uncurry_of_rightContinuous (hZmeas i)
        (hZright i)
    adapted := fun i =>
      _root_.Prove2MeSourceProof.h_845c55972b82cdb43dfb6421 (hZmeas i)
        (hZright i)
    cadlag_paths := Filter.Eventually.of_forall fun ω t =>
      ⟨tendsto_pi_nhds.mpr fun i => hZright i ω t, fun i => hZleft i ω t⟩
    sup_L2 := ?_ }, ?_⟩
  · rw [LevyStochCalc.Ito.Picard.bieleckiNorm_congr_ae 0 T hstepae,
      LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq 0 T]
    exact _root_.Prove2MeSourceProof.h_146d3b4e1dccf65e2e9025d2 W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas
      h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq h_μ_meas hμT hσT hγT
  · intro t
    exact (hstepae t).trans (LevyStochCalc.Ito.Picard.picardStepMod_ae_eq W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas
      h_σ_sq N hℱN x₀ h_γ_meas h_γ_progMeas h_γ_sq t)
end Modification

section SelfMap

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]

end SelfMap

end LevyStochCalc.Ito.Picard


