-- Prove2me | Definitions.Def_LevyStochCalc_Driver_GermIndep_F000
-- name    : LevyStochCalc_Driver_GermIndep_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:36:25.715026+00:00
-- url     : https://prove2.me/theorems/7455d14f-0857-40b6-96ea-2f958061b7bb
-- title:
--   Source declarations: LevyStochCalc.Driver.GermIndep
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.GermIndep. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_ValueSigma_F000
import Definitions.Def_LevyStochCalc_Poisson_ZeroIntensity_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The germ field of a Lévy driver

`Driver/ValueSigma.lean` gives the independence of `ℱ₊ 0` from the driver's data along a strictly
increasing grid of positive times. An arbitrary finite family of positive times is put in that
form by sorting it (`gridOf`), which turns the statement into one about arbitrary finite tuples.
Independence then passes to the supremum over finite subfamilies of the generators of `ℱ T`
(`indep_iSup_of_finset`), the two generators outside reach — Brownian values at non-positive times
and the part of a region in negative time — being almost surely constant and so dropping out.

## Main statements

* `LevyDriver.indep_valueTuple` — `ℱ₊ 0` against an arbitrary finite tuple of the driver's data.
* `LevyDriver.indep_rightCont_zero_filtration` — `ℱ₊ 0` against `ℱ T` for every `T > 0`.
* `LevyDriver.isTrivialSigma_rightCont_zero` — Blumenthal's 0-1 law itself.
* `LevyDriver.condExp_rightCont_nonpos` — the conditional expectation on `ℱ₊ s`, `s ≤ 0`, is the
  mean.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Driver

universe u v w

/-- A strictly increasing sequence of reals whose initial segment enumerates a nonempty finite
set in increasing order. -/
noncomputable def gridOf (T : Finset ℝ) (hT : T.Nonempty) : ℕ → ℝ := fun l =>
  if h : l < T.card then T.orderEmbOfFin rfl ⟨l, h⟩
  else T.max' hT + ((l - T.card + 1 : ℕ) : ℝ)
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)

end LevyDriver

end LevyStochCalc.Driver


