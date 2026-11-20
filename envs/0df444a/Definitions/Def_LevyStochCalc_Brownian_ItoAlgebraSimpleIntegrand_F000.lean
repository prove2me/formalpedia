-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F000
-- name    : LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:02:27.104081+00:00
-- url     : https://prove2.me/theorems/f1f4261c-5bf4-4f08-a41a-5676fbbc2be5
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Filtered_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F000
import Definitions.Def_LevyStochCalc_Probability_Progressive_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple integrands as integrands of the `L²` Brownian Itô integral

A simple integrand is uniformly bounded in both variables, jointly measurable, square-integrable
on every time window and, when its coefficients are adapted to a filtration, progressively
measurable, so it is an admissible integrand for the `L²` Itô integral in its own right; the two
elementary integrals of adapted simple integrands obey the Itô isometry for their difference at
an intermediate time, and the `L²` Itô integral of a simple integrand agrees almost everywhere
with its elementary integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- A simple integrand is uniformly bounded in both variables. -/
theorem SimplePredictable.exists_eval_bound {T : ℝ} (G : SimplePredictable Ω T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ω, |G.eval s ω| ≤ B := by
  classical
  choose M hM using G.ξ_bounded
  refine ⟨∑ i : Fin G.N, max (M i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _,
    fun s ω => ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  by_cases h : G.partition i.castSucc < s ∧ s ≤ G.partition i.succ
  · rw [if_pos h]; exact (hM i ω).trans (le_max_left _ _)
  · rw [if_neg h, abs_zero]; exact le_max_right _ _
section EvalSimple

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (hm : Measurable (Function.uncurry fun ω s => G.eval s ω))
  (hp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end EvalSimple

end LevyStochCalc.Brownian.Ito


