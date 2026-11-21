-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
-- name    : LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:24:56.630189+00:00
-- url     : https://prove2.me/theorems/1245c651-7cf1-426c-8c56-3565f944c1e1
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoL2CompletionQuadVar
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoL2CompletionQuadVar. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: isometry, right continuity and quadratic variation

The `L²`-isometry `∫⁻ ‖stochasticIntegralBrownian T‖₊² = ∫⁻ ∫⁻_{[0, T]} ‖H‖₊²`,
membership of the process in `L²(P)`, right `L²`-continuity of its time slices and
the resulting martingale property with respect to the right-continuation `ℱ₊` of
`ℱ`, and the compensator `∫_{[0, t]} (H ω u)² du` with the `ℱ`-martingale property
of the compensated square.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ in
/-- `F t ∈ L²(P)`. -/
lemma stochasticIntegralBrownian_memLp (t : ℝ) :
    MeasureTheory.MemLp (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global t) 2 P :=
  (MeasureTheory.Lp.memLp _).ae_eq
    (stochasticIntegralBrownian_ae_eq W ℱ hℱ H h_meas h_progMeas h_sq_int_global t).symm
end MasterSequence

end LevyStochCalc.Brownian.Ito


