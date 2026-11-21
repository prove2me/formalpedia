-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_MarkStepPolarised_F001
-- name    : LevyStochCalc_Poisson_MarkStepPolarised_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:52:51.920068+00:00
-- url     : https://prove2.me/theorems/cec86c80-a85b-4d6c-8adf-f40ac672df14
-- title:
--   Source declarations: LevyStochCalc.Poisson.MarkStepPolarised
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.MarkStepPolarised. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepWeight_F001
import Definitions.Def_SourceProof_d48a4c705b920c2354300189

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The bilinear form of the `L²` isometry for mark-step integrands

For two adapted mark-step integrands `G, G'` on a common time grid, the expectation of the
product of their compensated integrals up to a time `t ≥ 0` is the expectation of the time-mark
integral of the product of the integrands,
`E[(∫_0^t ∫_E G dÑ)(∫_0^t ∫_E G' dÑ)] = E[∫_E ∫_0^t G(s, e) G'(s, e) ds ν(de)]`, and the same
identity holds for the integrals over the whole horizon. It comes from the isometry for a
difference applied to the pairs `G, G'` and `G, G'.neg`, together with the polarisation identity
`4 a a' = (a + a') ^ 2 - (a - a') ^ 2`. Splitting the nested integral of that identity into its
two halves uses the boundedness of a mark-step integrand and the finite intensity of its mark
sets.

## Main statements

* `LevyStochCalc.Poisson.Compensated.MarkStep.integral_mul_at` — the bilinear identity up to a
  time `t ≥ 0`.
* `LevyStochCalc.Poisson.Compensated.MarkStep.integral_full_mul` — the bilinear identity for the
  integrals over the whole horizon.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Polarisation

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (hℱ : IsPoissonFiltration N ℱ) (G G' : MarkStep Ω E ν g)

include hℱ in
/-- The expectation of the product of the compensated integrals of two adapted mark-step
integrands on a common grid, over the whole horizon, is the expectation of the time-mark integral
of the product of the integrands. -/
theorem integral_full_mul (hG : G.Adapted ℱ) (hG' : G'.Adapted ℱ) {T : ℝ}
    (hT : g.horizon ≤ T) :
    ∫ ω, G.full N ω * G'.full N ω ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T,
          G.eval s e ω * G'.eval s e ω ∂volume ∂ν) ∂P := by
  have hT0 : 0 ≤ T := g.horizon_nonneg.trans hT
  have h := _root_.Prove2MeSourceProof.h_d48a4c705b920c2354300189 N hℱ G G' hG hG' hT0
  simp only [G.integral_eq_full_of_horizon_le N hT, G'.integral_eq_full_of_horizon_le N hT] at h
  exact h
end Polarisation

end MarkStep

end LevyStochCalc.Poisson.Compensated


