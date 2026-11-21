-- Prove2me | Definitions.Def_SourceProof_a8da103e0afd15e51015e74e
-- name    : SourceProof_a8da103e0afd15e51015e74e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:44:25.575447+00:00
-- url     : https://prove2.me/theorems/9709c53d-2488-41c6-8c5f-cd740d0ffe13
-- title:
--   LevyStochCalc source module: SourceProof_a8da103e0afd15e51015e74e
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.exists_markedPredictable_markedHorizonIntegrand` comes from the `LevyStochCalc.Poisson.PredictableIntegrand` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PredictableIntegrand_F000
import Definitions.Def_SourceProof_6bebe70af91e345e56c64c09

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissible marked integrands have predictable versions

An admissible marked integrand agrees almost everywhere with a predictable process; cutting that
process to the horizon keeps it predictable — the horizon strip is a countable union of windows
of finite mark measure — and makes it admissible, and the two compensated integrals agree almost
surely because the energy of their difference vanishes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

open LevyStochCalc.Probability


theorem _root_.Prove2MeSourceProof.h_a8da103e0afd15e51015e74e
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T)
    (G : MarkedHorizonIntegrand P ν ℱ T) :
    ∃ G' : MarkedHorizonIntegrand P ν ℱ T, MarkedPredictable ℱ ν G'.toFun ∧
      G'.integral N hℱ =ᵐ[P] G.integral N hℱ := by
  obtain ⟨ψ, hψpred, hψae⟩ := _root_.Prove2MeSourceProof.h_4f66e9c655448e033b3d860d N G.measurable_uncurry
    G.progressive hT G.energy_ne_top
  set ψ' : Ω → ℝ → E → ℝ :=
    fun ω s e => (Set.Ioc (0 : ℝ) T).indicator (fun _ => ψ ω s e) s with hψ'def
  have hψ'pred : LevyStochCalc.Probability.MarkedPredictable ℱ ν ψ' := LevyStochCalc.Poisson.Compensated.markedPredictable_indicator_Ioc hψpred T
  have hψ'meas : Measurable fun p : Ω × ℝ × E => ψ' p.1 p.2.1 p.2.2 :=
    hψ'pred.mono (LevyStochCalc.Probability.markedPredictableSigma_le ℱ ν) le_rfl
  have hψ'prog : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ' :=
    (_root_.Prove2MeSourceProof.h_6bebe70af91e345e56c64c09 hψ'pred)
  have hψ'ae : (fun p : Ω × ℝ × E => G.toFun p.1 p.2.1 p.2.2)
      =ᵐ[LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T] fun p : Ω × ℝ × E => ψ' p.1 p.2.1 p.2.2 := by
    refine hψae.trans ?_
    filter_upwards [LevyStochCalc.Poisson.Compensated.ae_mem_Ioc_markedEnergyMeasure (P := P) (ν := ν) hT.le] with p hp
    exact (Set.indicator_of_mem hp fun _ => ψ p.1 p.2.1 p.2.2).symm
  have hfin : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T ψ' ≠ ⊤ := by
    rw [LevyStochCalc.Poisson.Compensated.markedEnergy_eq_eLpNorm_sq hψ'meas T, ← eLpNorm_congr_ae hψ'ae,
      ← LevyStochCalc.Poisson.Compensated.markedEnergy_eq_eLpNorm_sq G.measurable_uncurry T]
    exact G.energy_ne_top
  have hvanish : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → ψ' ω s e = 0 := fun ω s e hs =>
    Set.indicator_of_notMem (fun h => hs ⟨h.1.le, h.2⟩) _
  refine ⟨⟨ψ', hψ'meas, hψ'prog, hvanish, hfin⟩, hψ'pred, ?_⟩
  have hzero : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ' ω s e - G.toFun ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P = 0 := by
    have hdiff : (fun p : Ω × ℝ × E => ψ' p.1 p.2.1 p.2.2 - G.toFun p.1 p.2.1 p.2.2)
        =ᵐ[LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T] fun _ => (0 : ℝ) := by
      filter_upwards [hψ'ae] with p hp
      rw [hp, sub_self]
    have hE : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => ψ' ω s e - G.toFun ω s e)
        = eLpNorm (fun p : Ω × ℝ × E => ψ' p.1 p.2.1 p.2.2 - G.toFun p.1 p.2.1 p.2.2) 2
          (LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T) ^ 2 :=
      LevyStochCalc.Poisson.Compensated.markedEnergy_eq_eLpNorm_sq (hψ'meas.sub G.measurable_uncurry) T
    have hz : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => ψ' ω s e - G.toFun ω s e) = 0 := by
      rw [hE, eLpNorm_congr_ae hdiff]
      simp
    exact hz
  have hiso := LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated N ℱ hℱ ψ' G.toFun hψ'meas G.measurable_uncurry
    hψ'prog G.progressive
    (LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.sq_int_global ⟨ψ', hψ'meas, hψ'prog, hvanish, hfin⟩)
    G.sq_int_global T hT
  rw [hzero] at hiso
  have hL1 : MemLp ((⟨ψ', hψ'meas, hψ'prog, hvanish, hfin⟩ :
      LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T).integral N hℱ) 2 P :=
    LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.memLp N hℱ _
  have hL2 : MemLp (G.integral N hℱ) 2 P := LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.memLp N hℱ G
  have hae : AEMeasurable (fun ω => (‖(⟨ψ', hψ'meas, hψ'prog, hvanish, hfin⟩ :
      LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T).integral N hℱ ω - G.integral N hℱ ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (((hL1.sub hL2).aestronglyMeasurable.aemeasurable).nnnorm).coe_nnreal_ennreal.pow_const 2
  filter_upwards [(lintegral_eq_zero_iff' hae).mp hiso] with ω hω
  have h2 : (‖(⟨ψ', hψ'meas, hψ'prog, hvanish, hfin⟩ :
      LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T).integral N hℱ ω - G.integral N hℱ ω‖₊ : ℝ≥0∞) = 0 :=
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp hω
  have h3 : (⟨ψ', hψ'meas, hψ'prog, hvanish, hfin⟩ :
      LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T).integral N hℱ ω - G.integral N hℱ ω = 0 := by
    simpa using h2
  linarith
end LevyStochCalc.Poisson.Compensated


