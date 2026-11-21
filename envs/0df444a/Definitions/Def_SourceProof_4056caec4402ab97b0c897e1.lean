-- Prove2me | Definitions.Def_SourceProof_4056caec4402ab97b0c897e1
-- name    : SourceProof_4056caec4402ab97b0c897e1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:44:35.199579+00:00
-- url     : https://prove2.me/theorems/79fb214b-a32f-42ff-9e28-cdcbd4087a2a
-- title:
--   LevyStochCalc source module: SourceProof_4056caec4402ab97b0c897e1
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.isTrivialSigma_rightCont_zero` comes from the `LevyStochCalc.Driver.GermIndep` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_933913e2a2f43e4d1189e911

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

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)


theorem _root_.Prove2MeSourceProof.h_4056caec4402ab97b0c897e1 :
    Probability.IsTrivialSigma P (D.filtration.rightCont 0) := by
  intro A hA
  have hle : D.filtration.rightCont 0 ≤ D.filtration 1 := by
    rw [Filtration.rightCont_eq_of_neBot_nhdsGT D.filtration 0]
    exact iInf₂_le (1 : ℝ) one_pos
  have h := (_root_.Prove2MeSourceProof.h_933913e2a2f43e4d1189e911 (T := 1) D) one_pos
  rw [Indep_iff] at h
  have hAA := h A A hA (hle A hA)
  rw [Set.inter_self] at hAA
  rcases eq_or_ne (P A) 0 with h0 | h0
  · exact Or.inl h0
  · refine Or.inr ?_
    have hone : P A * 1 = P A * P A := by rw [mul_one]; exact hAA
    exact ((ENNReal.mul_right_inj h0 (measure_ne_top P A)).1 hone).symm
end LevyDriver

end LevyStochCalc.Driver


