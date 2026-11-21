-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F001
-- name    : LevyStochCalc_Brownian_ItoAlgebraProduct_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:41:02.98088+00:00
-- url     : https://prove2.me/theorems/a00e1759-e6de-4375-8e61-fd6a8f0aadd0
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoAlgebraProduct
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoAlgebraProduct. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Products of simple integrands and elementary integrals against a process

Two simple integrands with a common final partition point multiply to a simple integrand carried
on their common refinement, whose evaluation is the pointwise product of the evaluations and
whose adaptedness is inherited; summing the increments of the elementary integral of one against
the coefficients of the other is the elementary integral of that product, and the difference
between an elementary integral and an `L²` Itô integral obeys the Itô isometry.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

private lemma min_min_of_le {a b t : ℝ} (h : a ≤ b) : min a (min b t) = min a t := by
  rw [← min_assoc, min_eq_left h]
private lemma min_min_of_le' {a b t : ℝ} (h : a ≤ b) : min b (min a t) = min a t := by
  rw [← min_assoc, min_eq_right h]
section SimpleVsGeneral

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end SimpleVsGeneral

end LevyStochCalc.Brownian.Ito


