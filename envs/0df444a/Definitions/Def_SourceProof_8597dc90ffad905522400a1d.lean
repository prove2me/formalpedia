-- Prove2me | Definitions.Def_SourceProof_8597dc90ffad905522400a1d
-- name    : SourceProof_8597dc90ffad905522400a1d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:37:42.169571+00:00
-- url     : https://prove2.me/theorems/054fd832-9e90-431f-952d-52967b394c8f
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Poisson.Compensated.exists_marked_progressive_energy_limit
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F001

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

theorem _root_.Prove2MeSourceProof.h_8597dc90ffad905522400a1d (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hm : ∀ n, Measurable fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2)
    (hp : ∀ n, Probability.MarkedProgressivelyMeasurable ℱ (φ n))
    (hz : ∀ n ω s e, s ∉ Set.Icc (0 : ℝ) T → φ n ω s e = 0)
    (hfin : ∀ n, markedEnergy P ν T (φ n) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      markedEnergy P ν T (fun ω s e => φ m ω s e - φ n ω s e) < ε) :
    ∃ ψ : Ω → ℝ → E → ℝ, Measurable (fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
      ∧ Probability.MarkedProgressivelyMeasurable ℱ ψ
      ∧ (∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → ψ ω s e = 0)
      ∧ markedEnergy P ν T ψ ≠ ⊤
      ∧ Tendsto (fun n => markedEnergy P ν T (fun ω s e => φ n ω s e - ψ ω s e)) atTop (𝓝 0) := by
  obtain ⟨g, hgMem, hgt⟩ := LevyStochCalc.Poisson.Compensated.exists_markedEnergy_limit hm hfin hcau
  have hMem : ∀ n, MemLp (fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2) 2
      (LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T) := fun n => LevyStochCalc.Poisson.Compensated.memLp_of_markedEnergy_ne_top (hm n) (hfin n)
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (μ := LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T) (p := 2) (by norm_num)
    (fun n => (hMem n).aestronglyMeasurable) hgMem.aestronglyMeasurable
    hgt).exists_seq_tendsto_ae
  have hKm : Measurable fun p : Ω × ℝ × E =>
      LevyStochCalc.Poisson.Compensated.limsupMarkedIntegrand φ ns p.1 p.2.1 p.2.2 := Measurable.limsup fun i => hm (ns i)
  have hKp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ (LevyStochCalc.Poisson.Compensated.limsupMarkedIntegrand φ ns) :=
    LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_limsup fun i => hp (ns i)
  have hKz : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → LevyStochCalc.Poisson.Compensated.limsupMarkedIntegrand φ ns ω s e = 0 := by
    intro ω s e hs
    have h0 : (fun i => φ (ns i) ω s e) = fun _ => (0 : ℝ) :=
      funext fun i => hz (ns i) ω s e hs
    rw [LevyStochCalc.Poisson.Compensated.limsupMarkedIntegrand, h0]
    exact limsup_const 0
  have hKg : (fun p : Ω × ℝ × E => LevyStochCalc.Poisson.Compensated.limsupMarkedIntegrand φ ns p.1 p.2.1 p.2.2)
      =ᵐ[LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T] g := by
    filter_upwards [hae] with p hp'
    exact hp'.limsup_eq
  have hKfin : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (LevyStochCalc.Poisson.Compensated.limsupMarkedIntegrand φ ns) ≠ ⊤ := by
    rw [LevyStochCalc.Poisson.Compensated.markedEnergy_eq_eLpNorm_sq hKm T, eLpNorm_congr_ae hKg]
    exact ENNReal.pow_ne_top hgMem.eLpNorm_lt_top.ne
  have hEq : ∀ n, LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => φ n ω s e - LevyStochCalc.Poisson.Compensated.limsupMarkedIntegrand φ ns ω s e)
      = eLpNorm ((fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2) - g) 2
        (LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T) ^ 2 := by
    intro n
    rw [LevyStochCalc.Poisson.Compensated.markedEnergy_eq_eLpNorm_sq ((hm n).sub hKm) T]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [hKg] with p h1
    simp only [Pi.sub_apply]
    rw [h1]
  refine ⟨LevyStochCalc.Poisson.Compensated.limsupMarkedIntegrand φ ns, hKm, hKp, hKz, hKfin, ?_⟩
  simp only [hEq]
  have hcont : Continuous fun x : ℝ≥0∞ => x ^ 2 := ENNReal.continuous_pow 2
  simpa [Function.comp_def] using (hcont.tendsto 0).comp hgt
end Complete

end LevyStochCalc.Poisson.Compensated


