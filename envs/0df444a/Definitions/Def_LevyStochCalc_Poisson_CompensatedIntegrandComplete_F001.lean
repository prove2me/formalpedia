-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F001
-- name    : LevyStochCalc_Poisson_CompensatedIntegrandComplete_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:33:06.67118+00:00
-- url     : https://prove2.me/theorems/daf40222-84ab-479a-9ba7-8cfe80c0068d
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedIntegrandComplete
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedIntegrandComplete. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F000
import Definitions.Def_SourceProof_f0c53d0eaa784ed729ffd61d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Completeness of the marked integrands

The marked energy of an integrand over a horizon is the square of its `L²`-seminorm for the
product of the sample measure, Lebesgue measure on the horizon and the mark measure. That space is
complete, so an energy-Cauchy sequence of admissible marked integrands has a limit; a pointwise
`limsup` along an almost-everywhere convergent subsequence provides a genuinely progressively
measurable representative of it.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Complete

variable {T : ℝ} {φ : ℕ → Ω → ℝ → E → ℝ}

omit [IsProbabilityMeasure P] in
/-- An energy-Cauchy sequence of marked integrands has an `L²`-limit on the product space. -/
theorem exists_markedEnergy_limit
    (hm : ∀ n, Measurable fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2)
    (hfin : ∀ n, markedEnergy P ν T (φ n) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      markedEnergy P ν T (fun ω s e => φ m ω s e - φ n ω s e) < ε) :
    ∃ g : Ω × ℝ × E → ℝ, MemLp g 2 (markedEnergyMeasure P ν T)
      ∧ Tendsto (fun n => eLpNorm
          ((fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2) - g) 2 (markedEnergyMeasure P ν T))
          atTop (𝓝 0) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hMem : ∀ n, MemLp (fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2) 2
      (markedEnergyMeasure P ν T) := fun n => memLp_of_markedEnergy_ne_top (hm n) (hfin n)
  have hcs : CauchySeq fun n => (hMem n).toLp fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2 := by
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcau (ε ^ 2) (by positivity)
    refine ⟨N, fun m hm' n hn' => ?_⟩
    rw [Lp.edist_def]
    have hcongr : eLpNorm
          ((((hMem m).toLp fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2) : Ω × ℝ × E → ℝ)
            - (((hMem n).toLp fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2) : Ω × ℝ × E → ℝ))
          2 (markedEnergyMeasure P ν T)
        = eLpNorm (fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2 - φ n p.1 p.2.1 p.2.2) 2
          (markedEnergyMeasure P ν T) := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hMem m).coeFn_toLp, (hMem n).coeFn_toLp] with p h1 h2
      simp only [Pi.sub_apply]
      rw [h1, h2]
    rw [hcongr]
    rcases lt_or_ge (eLpNorm (fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2 - φ n p.1 p.2.1 p.2.2)
      2 (markedEnergyMeasure P ν T)) ε with hlt' | hge
    · exact hlt'
    · exfalso
      have hsq : ε ^ 2 ≤ eLpNorm
          (fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2 - φ n p.1 p.2.1 p.2.2) 2
          (markedEnergyMeasure P ν T) ^ 2 := pow_le_pow_left' hge 2
      have hlt := hN m hm' n hn'
      rw [markedEnergy_eq_eLpNorm_sq ((hm m).sub (hm n)) T] at hlt
      exact absurd hlt (not_lt.mpr hsq)
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨(G : Ω × ℝ × E → ℝ), Lp.memLp G, ?_⟩
  have hlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ G).mp hG
  refine hlim.congr fun n => ?_
  refine eLpNorm_congr_ae ?_
  filter_upwards [(hMem n).coeFn_toLp] with p h1
  simp only [Pi.sub_apply]
  rw [h1]
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A pointwise `limsup` along `atTop` of countably many progressively measurable marked
processes is progressively measurable. -/
theorem markedProgressivelyMeasurable_limsup {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {φ : ℕ → Ω → ℝ → E → ℝ} (h : ∀ k, Probability.MarkedProgressivelyMeasurable ℱ (φ k)) :
    Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => limsup (fun k => φ k ω s e) atTop := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hind : (fun p : Ω × ℝ × E => (Set.Iic t).indicator
        (fun s => limsup (fun k => φ k p.1 s p.2.2) atTop) p.2.1)
      = fun p : Ω × ℝ × E =>
        limsup (fun k => (Set.Iic t).indicator (fun s => φ k p.1 s p.2.2) p.2.1) atTop := by
    funext p
    by_cases hp : p.2.1 ∈ Set.Iic t
    · simp only [Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, limsup_const]
  rw [hind]
  refine stronglyMeasurable_iff_measurable.mpr (Measurable.limsup fun k => ?_)
  exact (h k t).measurable
/-- The pointwise `limsup` of a subsequence of marked integrands. -/
noncomputable def limsupMarkedIntegrand (φ : ℕ → Ω → ℝ → E → ℝ) (ns : ℕ → ℕ) :
    Ω → ℝ → E → ℝ := fun ω s e => limsup (fun i => φ (ns i) ω s e) atTop
end Complete

end LevyStochCalc.Poisson.Compensated


