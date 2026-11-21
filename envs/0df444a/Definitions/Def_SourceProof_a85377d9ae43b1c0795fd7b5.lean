-- Prove2me | Definitions.Def_SourceProof_a85377d9ae43b1c0795fd7b5
-- name    : SourceProof_a85377d9ae43b1c0795fd7b5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:58:53.875259+00:00
-- url     : https://prove2.me/theorems/ece3d1dc-afff-44ab-9b83-914000193a2f
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.Ito.progressivelyMeasurable_mul_indIoc
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoPullOut_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pulling a past weight inside an Itô integral over a window

A bounded `ℱ_a`-measurable weight times the Itô integral of an integrand supported in `(a, b]` is
the Itô integral of the weighted integrand: the weight times the indicator is itself a simple
integrand, so this is associativity against a simple integrand.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_a85377d9ae43b1c0795fd7b5 (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M)
    (hVm : Measurable V) (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * indIoc Ω a b ω s := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hfun : (fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω 0 b ω s)
        = fun ω s => (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω := by
      funext ω s; rw [LevyStochCalc.Brownian.Ito.stepIocMul₀_eval]
    rw [hfun]
    exact (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).progressivelyMeasurable_eval ℱ
      (LevyStochCalc.Brownian.Ito.stepIocMul₀_adapt ℱ hab hVb hVm hVa)
  · have hfun : (fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s)
        = fun ω s => (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω := by
      funext ω s; rw [LevyStochCalc.Brownian.Ito.stepIocMul_eval]
    rw [hfun]
    exact (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).progressivelyMeasurable_eval ℱ
      (LevyStochCalc.Brownian.Ito.stepIocMul_adapt ℱ ha' hab hVb hVm hVa)
section PullOut

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end PullOut

end LevyStochCalc.Brownian.Ito


