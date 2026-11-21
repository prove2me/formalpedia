-- Prove2me | Definitions.Def_SourceProof_1783d6024dc5fa5c520e82bb
-- name    : SourceProof_1783d6024dc5fa5c520e82bb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:11:03.818065+00:00
-- url     : https://prove2.me/theorems/2a33d42b-d2f2-4115-b275-d665b1e1e0a3
-- title:
--   LevyStochCalc source module: SourceProof_1783d6024dc5fa5c520e82bb
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.masterApprox_evalNorm_tendsto` comes from the `LevyStochCalc.Brownian.ItoL2CompletionMaster` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F000
import Definitions.Def_SourceProof_186e21643bf26d9e554362b3
import Definitions.Def_SourceProof_f68e93dfb81b09358de9c4e9

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the master approximating sequence

The master sequence `masterApprox` of adapted simple predictable integrands on the
growing horizons `[0, n + 1]`, its Cauchy property in `L²(P)` uniformly on compact
time intervals, the limit `masterLp` and `stochasticIntegralBrownianLp` in
`Lp ℝ 2 P`, and the process `stochasticIntegralBrownian` together with its
adaptedness, vanishing on negative times and `ℱ`-martingale property.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)


theorem _root_.Prove2MeSourceProof.h_1783d6024dc5fa5c520e82bb {T : ℝ} (hT : 0 < T) :
    Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P)
      Filter.atTop
      (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set ν : MeasureTheory.Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hν
  set Hp : Ω × ℝ → ℝ := fun p => H p.1 p.2 with hHp
  set Gp : ℕ → Ω × ℝ → ℝ := fun n p =>
    (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval p.2 p.1 with hGp
  have hHp_meas : Measurable Hp := h_meas
  have hGp_meas : ∀ n, Measurable (Gp n) := fun n =>
    (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval_jointly_measurable
  -- Tonelli bridge: `eLpNorm f 2 (P⊗ν) ^ 2 = ∫⁻∫⁻_{[0,T]} ‖f(ω,·)‖²`.
  have hbridge : ∀ (f : Ω × ℝ → ℝ), Measurable f →
      MeasureTheory.eLpNorm f 2 (P.prod ν) ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    intro f hf
    rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq,
        MeasureTheory.lintegral_prod _
          (((hf.nnnorm.coe_nnreal_ennreal).pow_const 2).aemeasurable)]
  -- `eLpNorm < ⊤` from finiteness of the squared mass.
  have hfin : ∀ (f : Ω × ℝ → ℝ), Measurable f →
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) →
      MeasureTheory.eLpNorm f 2 (P.prod ν) < ⊤ := by
    intro f hf hfin
    refine lt_top_iff_ne_top.mpr (fun h => hfin ?_)
    rw [← hbridge f hf, h, ENNReal.top_rpow_of_pos (by norm_num)]
  have hHmemLp : MeasureTheory.MemLp Hp 2 (P.prod ν) :=
    ⟨hHp_meas.aestronglyMeasurable, hfin Hp hHp_meas (h_sq_int_global T hT).ne⟩
  have hGmemLp : ∀ n, MeasureTheory.MemLp (Gp n) 2 (P.prod ν) := fun n =>
    ⟨(hGp_meas n).aestronglyMeasurable, hfin (Gp n) (hGp_meas n)
      (_root_.Prove2MeSourceProof.h_186e21643bf26d9e554362b3 (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) T).ne⟩
  -- `Gp n → Hp` in `L²(P⊗ν)`.
  have hdiff : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν))
      Filter.atTop (nhds 0) := by
    have hsq : ∀ n, MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν) ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P := by
      intro n
      rw [hbridge (Gp n - Hp) ((hGp_meas n).sub hHp_meas)]
      refine lintegral_congr (fun ω =>
        MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_))
      rw [Pi.sub_apply, hGp, hHp, ← nnnorm_neg]
      congr 1; ring_nf
    have h2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν) ^ (2 : ℝ))
        Filter.atTop (nhds 0) := by
      simp_rw [hsq]
      exact _root_.Prove2MeSourceProof.h_f68e93dfb81b09358de9c4e9 (t := T) ℱ H h_meas h_progMeas h_sq_int_global
    have h3 := h2.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    refine h3.congr (fun n => ?_)
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  -- transfer to `Lp`, take norms.
  have hLp := (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => Gp n)
    (fun n => hGmemLp n) Hp hHmemLp).mpr hdiff
  have hnorm := hLp.enorm
  simp only [MeasureTheory.Lp.enorm_def] at hnorm
  have hnorm2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Gp n) 2 (P.prod ν))
      Filter.atTop (nhds (MeasureTheory.eLpNorm Hp 2 (P.prod ν))) := by
    rw [MeasureTheory.eLpNorm_congr_ae (MeasureTheory.MemLp.coeFn_toLp hHmemLp)] at hnorm
    refine hnorm.congr (fun n => ?_)
    exact MeasureTheory.eLpNorm_congr_ae (MeasureTheory.MemLp.coeFn_toLp (hGmemLp n))
  -- square and convert via the bridge.
  have := hnorm2.ennrpow_const 2
  simp_rw [hbridge _ (hGp_meas _)] at this
  rw [hbridge Hp hHp_meas] at this
  exact this
end MasterSequence

end LevyStochCalc.Brownian.Ito


