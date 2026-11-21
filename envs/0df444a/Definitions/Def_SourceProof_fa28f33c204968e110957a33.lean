-- Prove2me | Definitions.Def_SourceProof_fa28f33c204968e110957a33
-- name    : SourceProof_fa28f33c204968e110957a33
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:01:50.361471+00:00
-- url     : https://prove2.me/theorems/05da677f-7b58-4210-b287-bb2591f4d00c
-- title:
--   LevyStochCalc source module: SourceProof_fa28f33c204968e110957a33
-- statement:
--   The original source theorem `LevyStochCalc.Driver.strictMono_gridOf` comes from the `LevyStochCalc.Driver.GermIndep` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_GermIndep_F000

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

theorem _root_.Prove2MeSourceProof.h_fa28f33c204968e110957a33 (T : Finset ℝ) (hT : T.Nonempty) : StrictMono (gridOf T hT) := by
  intro a b hab
  by_cases ha : a < T.card <;> by_cases hb : b < T.card
  · simp only [LevyStochCalc.Driver.gridOf, dif_pos ha, dif_pos hb]
    exact (T.orderEmbOfFin rfl).strictMono (by exact hab)
  · simp only [LevyStochCalc.Driver.gridOf, dif_pos ha, dif_neg hb]
    have h1 : T.orderEmbOfFin rfl ⟨a, ha⟩ ≤ T.max' hT :=
      T.le_max' _ (T.orderEmbOfFin_mem rfl ⟨a, ha⟩)
    have h2 : (0 : ℝ) < ((b - T.card + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos (b - T.card)
    linarith
  · exact absurd hab (by omega)
  · simp only [LevyStochCalc.Driver.gridOf, dif_neg ha, dif_neg hb]
    have h : ((a - T.card + 1 : ℕ) : ℝ) < ((b - T.card + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : a - T.card + 1 < b - T.card + 1)
    linarith
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)

end LevyDriver

end LevyStochCalc.Driver


