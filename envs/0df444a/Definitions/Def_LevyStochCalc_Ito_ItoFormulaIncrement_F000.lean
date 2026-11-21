-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaIncrement_F000
-- name    : LevyStochCalc_Ito_ItoFormulaIncrement_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:27:30.812213+00:00
-- url     : https://prove2.me/theorems/06a9b4e4-abed-459e-ae14-6b99da311b36
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaIncrement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaIncrement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaShift_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaStoppedLimit_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaStoppedLimit_F001
import Definitions.Def_LevyStochCalc_Ito_VectorItoProcessDiff_F000
import Definitions.Def_SourceProof_426ff55101b7b0df983e6be6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for the increment of a path between two stopping times

Subtracting Itô's formula along the path stopped at one stopping time from Itô's formula along
the path stopped at another recombines into a single formula for the increment between the two
clipped horizons: each Lebesgue integral becomes the integral of the increment of the cut-off
integrand, and the two Itô integrals become the single Itô integral of that increment.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_sub` — the Itô integral of the
  increment between two cut-offs of an integrand is the difference of the two Itô integrals.
* `LevyStochCalc.Brownian.Ito.ae_integrableOn_stopped_Ioc` — a cut-off integrand of finite energy
  is almost surely integrable on a bounded window.
* `LevyStochCalc.Brownian.Ito.ae_integrableOn_stopped_Ioc_of_ae_integrableOn` — cutting off at a
  stopping time preserves almost sure integrability on a bounded window.
* `LevyStochCalc.Brownian.Ito.itoFormula_between` — Itô's formula for the increment of a path
  between two stopping times.
* `LevyStochCalc.Brownian.Ito.itoFormula_stopped_general_shift` — Itô's formula along a path
  stopped at an arbitrary stopping time, for a function translated by a fixed vector.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_shift` — the increment formula for a function
  translated by a fixed vector.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section IncrementAdmissible

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- The increment between the cut-offs of an integrand at two stopping times has measurable
uncurrying. -/
theorem measurable_uncurry_stopped_sub {ℱ : Filtration ℝ mΩ} {σ τ : Ω → WithTop ℝ}
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K)) :
    Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ K ω s - Probability.stopped σ K ω s) :=
  (Probability.measurable_uncurry_stopped hτ hmK).sub
    (Probability.measurable_uncurry_stopped hσ hmK)
/-- The increment between the cut-offs of an integrand at two stopping times is progressively
measurable. -/
theorem progressivelyMeasurable_stopped_sub {ℱ : Filtration ℝ mΩ} {σ τ : Ω → WithTop ℝ}
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {K : Ω → ℝ → ℝ} (hpK : Probability.ProgressivelyMeasurable ℱ K) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ K ω s - Probability.stopped σ K ω s :=
  (_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ hpK).sub
    (_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hσ hpK)
end IncrementAdmissible

section IncrementEnergy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- The increment between the cut-offs of an integrand at two stopping times has finite energy on
every window carrying finite energy of the integrand. -/
theorem energy_stopped_sub_lt_top {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K))
    (hqK : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ K ω s - Probability.stopped σ K ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤ :=
  _root_.Prove2MeSourceProof.h_700488d66fa58fc241f21293 (fun _ _ => sq_nnnorm_sub_le_two_mul _ _)
    (Probability.measurable_uncurry_stopped hτ hmK)
    (Probability.measurable_uncurry_stopped hσ hmK)
    (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ K ω s) hqK)
    (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le σ K ω s) hqK)
omit [IsProbabilityMeasure P] in
/-- A cut-off integrand of finite energy is almost surely integrable on a bounded window. -/
theorem ae_integrableOn_stopped_Ioc {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {τ : Ω → WithTop ℝ} (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K))
    (hqK : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, MeasureTheory.IntegrableOn
      (Probability.stopped τ K ω) (Set.Ioc (0 : ℝ) T) volume := by
  have hq := energy_lt_top_of_abs_le
    (fun ω s => Probability.abs_stopped_le τ K ω s) hqK T hT
  filter_upwards [ae_integrableOn_of_energy_lt_top
    (Probability.measurable_uncurry_stopped hτ hmK) hq] with ω hω
  exact hω.mono_set Set.Ioc_subset_Icc_self
omit [IsProbabilityMeasure P] in
/-- An integrand almost surely integrable on a bounded window stays almost surely integrable
there after being cut off at a stopping time. -/
theorem ae_integrableOn_stopped_Ioc_of_ae_integrableOn {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {τ : Ω → WithTop ℝ} (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K)) {T : ℝ}
    (hK : ∀ᵐ ω ∂P, MeasureTheory.IntegrableOn (K ω) (Set.Ioc (0 : ℝ) T) volume) :
    ∀ᵐ ω ∂P, MeasureTheory.IntegrableOn
      (Probability.stopped τ K ω) (Set.Ioc (0 : ℝ) T) volume := by
  filter_upwards [hK] with ω hω
  refine MeasureTheory.Integrable.mono hω ((Measurable.of_uncurry_left
    (Probability.measurable_uncurry_stopped hτ hmK)).aestronglyMeasurable) ?_
  filter_upwards with s
  simpa only [Real.norm_eq_abs] using Probability.abs_stopped_le τ K ω s
end IncrementEnergy

section IncrementItoIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **The Itô integral of the increment of an integrand between two stopping times.** It is the
difference of the Itô integrals of the integrand cut off at each of the two times. -/
theorem stochasticIntegralBrownian_stopped_sub
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K))
    (hpK : Probability.ProgressivelyMeasurable ℱ K)
    (hqK : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped τ K ω s - Probability.stopped σ K ω s)
        (measurable_uncurry_stopped_sub hσ hτ hmK)
        (progressivelyMeasurable_stopped_sub hσ hτ hpK)
        (energy_stopped_sub_lt_top hσ hτ hmK hqK) T
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ K)
          (Probability.measurable_uncurry_stopped hτ hmK)
          (_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ hpK)
          (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ K ω s) hqK) T ω
        - stochasticIntegralBrownian W ℱ hℱ (Probability.stopped σ K)
          (Probability.measurable_uncurry_stopped hσ hmK)
          (_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hσ hpK)
          (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le σ K ω s) hqK) T ω :=
  _root_.Prove2MeSourceProof.h_426ff55101b7b0df983e6be6 W ℱ hℱ
    (Probability.measurable_uncurry_stopped hτ hmK)
    (Probability.measurable_uncurry_stopped hσ hmK)
    (_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ hpK)
    (_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hσ hpK)
    (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ K ω s) hqK)
    (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le σ K ω s) hqK)
    (measurable_uncurry_stopped_sub hσ hτ hmK)
    (progressivelyMeasurable_stopped_sub hσ hτ hpK)
    (energy_stopped_sub_lt_top hσ hτ hmK hqK) hT
end IncrementItoIntegral

section Between

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end Between

end LevyStochCalc.Brownian.Ito


