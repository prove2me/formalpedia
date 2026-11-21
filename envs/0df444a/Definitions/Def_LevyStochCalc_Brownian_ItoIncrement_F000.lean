-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F000
-- name    : LevyStochCalc_Brownian_ItoIncrement_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:50:15.38854+00:00
-- url     : https://prove2.me/theorems/93fc9eb1-6a08-4fe9-8daf-4413ca004f40
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoIncrement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoIncrement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F002
import Definitions.Def_SourceProof_29dfa31cfdf118b2f60dc2a9

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô integral of an indicator is a Brownian increment

The integrand `1_{(a, b]}` is simple, so its `L²` Itô integral up to a time `t` is the elementary
integral `W_{b ∧ t} − W_{a ∧ t}`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Indicator

/-- The indicator integrand of a time window, as a process constant in the sample point. -/
noncomputable def indIoc (Ω) [MeasurableSpace Ω] (a b : ℝ) : Ω → ℝ → ℝ :=
  fun _ s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s
theorem indIoc_le_one (a b : ℝ) (ω : Ω) (s : ℝ) : |indIoc Ω a b ω s| ≤ 1 := by
  unfold indIoc
  by_cases h : s ∈ Set.Ioc a b
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num
theorem measurable_uncurry_indIoc (a b : ℝ) :
    Measurable (Function.uncurry (indIoc Ω a b)) :=
  ((measurable_const.indicator measurableSet_Ioc).comp measurable_snd)
theorem progressivelyMeasurable_indIoc (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b) := by
  have hfun : indIoc Ω a b = fun ω s => (stepIoc Ω ha hab).eval s ω := by
    funext ω s; rw [stepIoc_eval]; rfl
  rw [hfun]
  exact (stepIoc Ω ha hab).progressivelyMeasurable_eval ℱ (stepIoc_adapt ℱ ha hab)
theorem progressivelyMeasurable_indIoc₀ (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ}
    (hb : 0 < b) : Probability.ProgressivelyMeasurable ℱ (indIoc Ω 0 b) := by
  have hfun : indIoc Ω 0 b = fun ω s => (stepIoc₀ Ω hb).eval s ω := by
    funext ω s; rw [_root_.Prove2MeSourceProof.h_29dfa31cfdf118b2f60dc2a9]; rfl
  rw [hfun]
  exact (stepIoc₀ Ω hb).progressivelyMeasurable_eval ℱ (stepIoc₀_adapt ℱ hb)
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end Indicator

end LevyStochCalc.Brownian.Ito


