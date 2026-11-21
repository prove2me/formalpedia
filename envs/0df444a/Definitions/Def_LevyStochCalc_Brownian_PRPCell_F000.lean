-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_PRPCell_F000
-- name    : LevyStochCalc_Brownian_PRPCell_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:56:49.891309+00:00
-- url     : https://prove2.me/theorems/17d2c42a-634d-4242-8569-7c9bec8209fe
-- title:
--   Source declarations: LevyStochCalc.Brownian.PRPCell
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.PRPCell. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoVersionExists_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoVersionExists_F001
import Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F001
import Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# One window of the Brownian predictable representation

A square-integrable weight orthogonal to every Itô integral, multiplied by a bounded weight
measurable before a window and having mean zero, stays orthogonal to the character of the
Brownian increment across that window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The zero process is progressively measurable. -/
theorem progressivelyMeasurable_zero (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) := by
  intro t
  have h : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun _ => (0 : ℝ)) p.2)
      = fun _ : Ω × ℝ => (0 : ℝ) := by
    funext p
    simp [Set.indicator_apply]
  rw [h]
  exact stronglyMeasurable_const
section Cell

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

end Cell

end LevyStochCalc.Brownian.Ito


