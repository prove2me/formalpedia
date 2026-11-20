-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_MartingaleQuadVar_F001
-- name    : LevyStochCalc_Brownian_MartingaleQuadVar_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:39:13.561389+00:00
-- url     : https://prove2.me/theorems/7cf97b2e-206f-40aa-8017-34ebc51cae3a
-- title:
--   LevyStochCalc source module: LevyStochCalc.Brownian.MartingaleQuadVar
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Brownian.MartingaleQuadVar in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_MartingaleCondExp_F001
import Definitions.Def_SourceProof_a157dd277ff36750db5f28f0

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian martingale property and quadratic variation

Brownian motion is a martingale for its natural filtration, hence for any filtration to which it
is adapted with independent increments, and its quadratic variation is `⟨W⟩_t = t`: the process
`W_t² − t` is again a martingale. The identity `(dW)² = dt` it records is the second-order term
of the Itô formula.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Martingale

universe u

section MartingaleAndQuadVar
variable {Ω : Type u} [MeasurableSpace Ω]

/-- Brownian motion is a martingale with respect to some filtration, namely its natural
filtration. -/
theorem brownian_martingale
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale (fun t : ℝ => W.W t) F P :=
  ⟨naturalFiltration W, _root_.Prove2MeSourceProof.h_a157dd277ff36750db5f28f0 W⟩
end MartingaleAndQuadVar

end LevyStochCalc.Brownian.Martingale


