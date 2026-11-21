-- Prove2me | Definitions.Def_SourceProof_96968c8d5a5450421d19e3bc
-- name    : SourceProof_96968c8d5a5450421d19e3bc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:18:59.634997+00:00
-- url     : https://prove2.me/theorems/dd033103-87ad-4540-8ccd-3489ba0149ae
-- title:
--   LevyStochCalc source module: SourceProof_96968c8d5a5450421d19e3bc
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.integral_weight_zero_sq` comes from the `LevyStochCalc.Poisson.MarkStepWeight` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepWeight_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Sums, negations and weightings of mark-step integrands

Two mark-step integrands on a common time grid are added by concatenating their mark
families (`MarkStep.append`), and a mark-step integrand is negated coefficientwise
(`MarkStep.neg`); both operations act additively on the compensated integral and on the
integrand, so the `L²` isometry applies to differences. Multiplying the coefficients from a
given piece on by a bounded measurable weight `w`, and zeroing the earlier ones
(`MarkStep.weight`), yields the isometry for the weighted increment of the integral over a
grid interval.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Append

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G G' : MarkStep Ω E ν g)

end Append

section Weight

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w)

include hw hwm in
include hℱ in

theorem _root_.Prove2MeSourceProof.h_96968c8d5a5450421d19e3bc (hG : G.Adapted ℱ) {t : ℝ} (ht : 0 ≤ t)
    (hwa : @StronglyMeasurable Ω ℝ _ (ℱ 0) w) :
    ∫ ω, (w ω * G.integral N t ω) ^ 2 ∂P
      = ∫ ω, (w ω) ^ 2 * (∫ e, ∫ s in Set.Icc (0 : ℝ) t,
          (G.eval s e ω) ^ 2 ∂volume ∂ν) ∂P := by
  have hwa' : @StronglyMeasurable Ω ℝ _ (ℱ ((g.clamp t ht).p 0)) w := by
    change @StronglyMeasurable Ω ℝ _ (ℱ (min (g.p 0) t)) w
    rwa [g.p_zero, min_eq_left ht]
  have key := ((G.clamp t ht).weight w hw hwm 0).integral_full_sq N hℱ
    ((hG.clamp t ht).weight hw hwm hwa') (g.clamp_horizon_le t ht)
  simp_rw [(G.clamp t ht).full_weight_zero N hw hwm, (G.clamp t ht).eval_weight_zero hw hwm,
    ← (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_a7deec5abe53c22fffa52848 p2mMethodArg0 G) N t ht, (_root_.Prove2MeSourceProof.h_24d7e98c77e2168bb8fc8995 G) t ht] at key
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  beta_reduce
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  beta_reduce
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  rw [if_pos hs.2]
  ring
end Weight

end MarkStep

end LevyStochCalc.Poisson.Compensated


