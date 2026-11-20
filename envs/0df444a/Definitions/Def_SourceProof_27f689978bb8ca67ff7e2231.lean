-- Prove2me | Definitions.Def_SourceProof_27f689978bb8ca67ff7e2231
-- name    : SourceProof_27f689978bb8ca67ff7e2231
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:35:20.59539+00:00
-- url     : https://prove2.me/theorems/0eb330fb-4dca-4649-9b50-07dc7ddf2695
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.Ito.exists_progressive_energy_limit
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F001
import Definitions.Def_LevyStochCalc_Probability_Progressive_F000
import Definitions.Def_SourceProof_f0c53d0eaa784ed729ffd61d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Completeness of the admissible integrands on a horizon

The energy of an integrand over `[0, T]` is the square of its `L²`-seminorm for the product of
the sample measure with Lebesgue measure on the horizon. A sequence of integrands that is Cauchy
for that energy therefore has an `L²`-limit, and the pointwise `limsup` of an almost everywhere
convergent subsequence is a representative of that limit which is again progressively measurable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Complete

variable {T : ℝ} {H : ℕ → Ω → ℝ → ℝ}

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_27f689978bb8ca67ff7e2231 (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hm : ∀ n, Measurable (Function.uncurry (H n)))
    (hp : ∀ n, Probability.ProgressivelyMeasurable ℱ (H n))
    (hz : ∀ n ω s, s ∉ Set.Icc (0 : ℝ) T → H n ω s = 0)
    (hfin : ∀ n, energy P T (H n) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      energy P T (fun ω s => H m ω s - H n ω s) < ε) :
    ∃ K : Ω → ℝ → ℝ, Measurable (Function.uncurry K)
      ∧ Probability.ProgressivelyMeasurable ℱ K
      ∧ (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → K ω s = 0)
      ∧ energy P T K ≠ ⊤
      ∧ Tendsto (fun n => energy P T (fun ω s => H n ω s - K ω s)) atTop (𝓝 0) := by
  obtain ⟨g, hgMem, hgt⟩ := LevyStochCalc.Brownian.Ito.exists_energy_limit hm hfin hcau
  have hMem : ∀ n, MemLp (fun p : Ω × ℝ => H n p.1 p.2) 2 (LevyStochCalc.Brownian.Ito.energyMeasure P T) :=
    fun n => LevyStochCalc.Brownian.Ito.memLp_of_energy_ne_top (hm n) (hfin n)
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (μ := LevyStochCalc.Brownian.Ito.energyMeasure P T) (p := 2)
    (by norm_num) (fun n => (hMem n).aestronglyMeasurable)
    hgMem.aestronglyMeasurable hgt).exists_seq_tendsto_ae
  have hKm : Measurable (Function.uncurry (LevyStochCalc.Brownian.Ito.limsupIntegrand H ns)) :=
    Measurable.limsup fun i => hm (ns i)
  have hKp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (LevyStochCalc.Brownian.Ito.limsupIntegrand H ns) :=
    _root_.Prove2MeSourceProof.h_f0c53d0eaa784ed729ffd61d fun i => hp (ns i)
  have hKz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → LevyStochCalc.Brownian.Ito.limsupIntegrand H ns ω s = 0 := by
    intro ω s hs
    have h0 : (fun i => H (ns i) ω s) = fun _ => (0 : ℝ) := funext fun i => hz (ns i) ω s hs
    rw [LevyStochCalc.Brownian.Ito.limsupIntegrand, h0]
    exact limsup_const 0
  have hKg : (fun p : Ω × ℝ => LevyStochCalc.Brownian.Ito.limsupIntegrand H ns p.1 p.2) =ᵐ[LevyStochCalc.Brownian.Ito.energyMeasure P T] g := by
    filter_upwards [hae] with p hp'
    exact hp'.limsup_eq
  have hKfin : LevyStochCalc.Brownian.Ito.energy P T (LevyStochCalc.Brownian.Ito.limsupIntegrand H ns) ≠ ⊤ := by
    rw [LevyStochCalc.Brownian.Ito.energy_eq_eLpNorm_sq hKm T, eLpNorm_congr_ae hKg]
    exact ENNReal.pow_ne_top hgMem.eLpNorm_lt_top.ne
  have hEq : ∀ n, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => H n ω s - LevyStochCalc.Brownian.Ito.limsupIntegrand H ns ω s)
      = eLpNorm ((fun p : Ω × ℝ => H n p.1 p.2) - g) 2 (LevyStochCalc.Brownian.Ito.energyMeasure P T) ^ 2 := by
    intro n
    rw [LevyStochCalc.Brownian.Ito.energy_eq_eLpNorm_sq ((hm n).sub hKm) T]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [hKg] with p h1
    simp only [Pi.sub_apply]
    rw [h1]
  refine ⟨LevyStochCalc.Brownian.Ito.limsupIntegrand H ns, hKm, hKp, hKz, hKfin, ?_⟩
  simp only [hEq]
  have hcont : Continuous fun x : ℝ≥0∞ => x ^ 2 := ENNReal.continuous_pow 2
  simpa [Function.comp_def] using (hcont.tendsto 0).comp hgt
end Complete

end LevyStochCalc.Brownian.Ito


