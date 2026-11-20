-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F000
-- name    : LevyStochCalc_Poisson_CompensatedIntegrandComplete_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:19:14.142103+00:00
-- url     : https://prove2.me/theorems/05dc28f6-444a-4170-9461-1ef0e1bb8523
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedIntegrandComplete
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedIntegrandComplete. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F001
import Definitions.Def_LevyStochCalc_Probability_Progressive_F002

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

/-- The product of the sample measure, Lebesgue measure on the horizon and the mark measure. -/
noncomputable def markedEnergyMeasure (P : Measure Ω) (ν : Measure E) (T : ℝ) :
    Measure (Ω × ℝ × E) :=
  P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)
/-- The energy of a marked integrand over the horizon `[0, T]`. -/
noncomputable def markedEnergy (P : Measure Ω) (ν : Measure E) (T : ℝ) (φ : Ω → ℝ → E → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
omit [IsProbabilityMeasure P] in
/-- The marked energy is the square of the `L²`-seminorm on the product space. -/
theorem markedEnergy_eq_eLpNorm_sq {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) (T : ℝ) :
    markedEnergy P ν T φ
      = eLpNorm (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (markedEnergyMeasure P ν T) ^ 2 := by
  have hme : Measurable fun p : Ω × ℝ × E => (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    ((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2
  rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral, markedEnergyMeasure, markedEnergy,
    lintegral_prod _ hme.aemeasurable]
  refine lintegral_congr fun ω => ?_
  exact (lintegral_prod (μ := volume.restrict (Set.Icc (0 : ℝ) T)) (ν := ν)
    (fun y : ℝ × E => (‖φ ω y.1 y.2‖₊ : ℝ≥0∞) ^ 2)
    (hme.comp (measurable_prodMk_left (x := ω))).aemeasurable).symm
omit [IsProbabilityMeasure P] in
/-- A marked integrand of finite energy is square integrable on the product space. -/
theorem memLp_of_markedEnergy_ne_top {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) {T : ℝ}
    (hfin : markedEnergy P ν T φ ≠ ⊤) :
    MemLp (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (markedEnergyMeasure P ν T) := by
  refine ⟨hm.stronglyMeasurable.aestronglyMeasurable, ?_⟩
  refine lt_top_iff_ne_top.mpr fun hcon => hfin ?_
  rw [markedEnergy_eq_eLpNorm_sq hm T, hcon]
  simp
section Complete

variable {T : ℝ} {φ : ℕ → Ω → ℝ → E → ℝ}

end Complete

end LevyStochCalc.Poisson.Compensated


