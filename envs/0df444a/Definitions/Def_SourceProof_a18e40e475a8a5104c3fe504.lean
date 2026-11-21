-- Prove2me | Definitions.Def_SourceProof_a18e40e475a8a5104c3fe504
-- name    : SourceProof_a18e40e475a8a5104c3fe504
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:53:45.499916+00:00
-- url     : https://prove2.me/theorems/8098e11e-efc2-419f-a1d7-5a6ee4e7c0fc
-- title:
--   LevyStochCalc source module: SourceProof_a18e40e475a8a5104c3fe504
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.exists_predictable_horizonIntegrand` comes from the `LevyStochCalc.Brownian.PredictableIntegrand` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PredictableIntegrand_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissible integrands have predictable versions

An admissible integrand agrees almost everywhere with a predictable process; cutting that process
to the horizon keeps it predictable and makes it admissible, and the two integrals agree almost
surely because the energy of their difference vanishes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

open LevyStochCalc.Probability


theorem _root_.Prove2MeSourceProof.h_a18e40e475a8a5104c3fe504 (W : LevyStochCalc.Brownian.BrownianMotion P)
    (hℱ : IsBrownianFiltration W ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t) {T : ℝ} (hT : 0 < T)
    (G : HorizonIntegrand P ℱ T) :
    ∃ G' : HorizonIntegrand P ℱ T, Predictable ℱ G'.toFun ∧
      G'.integral W hℱ =ᵐ[P] G.integral W hℱ := by
  obtain ⟨K, hKpred, hKae⟩ :=
    _root_.Prove2MeSourceProof.h_ab7eaa8ef4ca09c9e29c494e ℱ G.measurable_uncurry G.progressive hT G.energy_ne_top
  set K' : Ω → ℝ → ℝ := fun ω s => (Set.Ioc (0 : ℝ) T).indicator (fun _ => K ω s) s with hK'def
  have hK'pred : LevyStochCalc.Probability.Predictable ℱ K' := LevyStochCalc.Brownian.Ito.predictable_indicator_Ioc hKpred hT.le
  have hK'meas : Measurable (Function.uncurry K') := LevyStochCalc.Brownian.Ito.measurable_uncurry_of_predictable hK'pred
  have hK'prog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ K' := hK'pred.progressivelyMeasurable hℱ0
  have hK'ae : (fun p : Ω × ℝ => G.toFun p.1 p.2)
      =ᵐ[LevyStochCalc.Brownian.Ito.energyMeasure P T] fun p : Ω × ℝ => K' p.1 p.2 := by
    refine hKae.trans ?_
    filter_upwards [LevyStochCalc.Brownian.Ito.ae_mem_Ioc_energyMeasure (P := P) hT.le] with p hp
    exact (Set.indicator_of_mem hp fun _ => K p.1 p.2).symm
  have hfin : LevyStochCalc.Brownian.Ito.energy P T K' ≠ ⊤ := by
    rw [LevyStochCalc.Brownian.Ito.energy_eq_eLpNorm_sq hK'meas T, ← eLpNorm_congr_ae hK'ae,
      ← LevyStochCalc.Brownian.Ito.energy_eq_eLpNorm_sq G.measurable_uncurry T]
    exact G.energy_ne_top
  have hvanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → K' ω s = 0 := fun ω s hs =>
    Set.indicator_of_notMem (fun h => hs ⟨h.1.le, h.2⟩) _
  refine ⟨⟨K', hK'meas, hK'prog, hvanish, hfin⟩, hK'pred, ?_⟩
  have hzero : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K' ω s - G.toFun ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P = 0 := by
    have hdiff : (fun p : Ω × ℝ => K' p.1 p.2 - G.toFun p.1 p.2)
        =ᵐ[LevyStochCalc.Brownian.Ito.energyMeasure P T] fun _ => (0 : ℝ) := by
      filter_upwards [hK'ae] with p hp
      rw [hp, sub_self]
    have hE : LevyStochCalc.Brownian.Ito.energy P T (fun ω s => K' ω s - G.toFun ω s)
        = eLpNorm (fun p : Ω × ℝ => K' p.1 p.2 - G.toFun p.1 p.2) 2 (LevyStochCalc.Brownian.Ito.energyMeasure P T) ^ 2 :=
      LevyStochCalc.Brownian.Ito.energy_eq_eLpNorm_sq (hK'meas.sub G.measurable_uncurry) T
    have : LevyStochCalc.Brownian.Ito.energy P T (fun ω s => K' ω s - G.toFun ω s) = 0 := by
      rw [hE, eLpNorm_congr_ae hdiff]
      simp
    exact this
  have hiso := _root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 W ℱ hℱ K' G.toFun hK'meas
    G.measurable_uncurry hK'prog G.progressive
    (LevyStochCalc.Brownian.Ito.HorizonIntegrand.sq_int_global ⟨K', hK'meas, hK'prog, hvanish, hfin⟩) G.sq_int_global hT
  rw [hzero] at hiso
  have hL1 : MemLp ((⟨K', hK'meas, hK'prog, hvanish, hfin⟩ :
      LevyStochCalc.Brownian.Ito.HorizonIntegrand P ℱ T).integral W hℱ) 2 P := LevyStochCalc.Brownian.Ito.HorizonIntegrand.memLp W hℱ _
  have hL2 : MemLp (G.integral W hℱ) 2 P := LevyStochCalc.Brownian.Ito.HorizonIntegrand.memLp W hℱ G
  have hae : AEMeasurable (fun ω => (‖(⟨K', hK'meas, hK'prog, hvanish, hfin⟩ :
      LevyStochCalc.Brownian.Ito.HorizonIntegrand P ℱ T).integral W hℱ ω - G.integral W hℱ ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (((hL1.sub hL2).aestronglyMeasurable.aemeasurable).nnnorm).coe_nnreal_ennreal.pow_const 2
  filter_upwards [(lintegral_eq_zero_iff' hae).mp hiso] with ω hω
  have h2 : (‖(⟨K', hK'meas, hK'prog, hvanish, hfin⟩ :
      LevyStochCalc.Brownian.Ito.HorizonIntegrand P ℱ T).integral W hℱ ω - G.integral W hℱ ω‖₊ : ℝ≥0∞) = 0 :=
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp hω
  have h3 : (⟨K', hK'meas, hK'prog, hvanish, hfin⟩ :
      LevyStochCalc.Brownian.Ito.HorizonIntegrand P ℱ T).integral W hℱ ω - G.integral W hℱ ω = 0 := by simpa using h2
  linarith
end LevyStochCalc.Brownian.Ito


