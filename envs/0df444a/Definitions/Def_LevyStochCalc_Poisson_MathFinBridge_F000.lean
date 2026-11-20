-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_MathFinBridge_F000
-- name    : LevyStochCalc_Poisson_MathFinBridge_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:17:32.221185+00:00
-- url     : https://prove2.me/theorems/58866326-2c61-45f7-a1ae-8f62b45086a8
-- title:
--   Source declarations: LevyStochCalc.Poisson.MathFinBridge
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.MathFinBridge. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_IndependentScattering_F000
import Definitions.Def_MathFin_Foundations_PoissonCompensatedIntegralOperator_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bridge to formal-mathfin's Poisson random measure

`MathFin.PoissonRandomMeasure` (raphaelrrcoelho/formal-mathfin) carries the same counting
measures, measurability and Poisson laws as `LevyStochCalc.Poisson.PoissonRandomMeasure`, with
independent scattering in σ-algebra form; the latter is `indep_of_disjoint_region` here, so every
Poisson random measure of this library is one of theirs. Through the bridge, their Itô–Lévy `L²`
isometry on the closure of marked simple integrands (`MathFin.itoLevyIntegralL2_norm`) applies to
ours.

## Main definitions

* `PoissonRandomMeasure.toMathFin` — the bridge.
* `PoissonRandomMeasure.itoLevyIntegralL2_norm` — the isometry, read back over this library's
  Poisson random measures.
-/

universe u v w

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

namespace PoissonRandomMeasure

/-- A Poisson random measure of this library, viewed as one of formal-mathfin's. -/
def toMathFin (N : PoissonRandomMeasure.{u, v, w} P ν) : MathFin.PoissonRandomMeasure P ν where
  N := N.N
  measurable_eval := N.measurable_eval
  poisson_law hB hfin := N.poisson_law hB hfin
  indep_of_disjoint_region := N.indep_of_disjoint_region
@[simp] theorem toMathFin_N (N : PoissonRandomMeasure.{u, v, w} P ν) : N.toMathFin.N = N.N := rfl
/-- The compensated-Poisson integral of formal-mathfin is an `L²` isometry on the closure of the
marked simple integrands, for every Poisson random measure of this library. -/
theorem itoLevyIntegralL2_norm (N : PoissonRandomMeasure.{u, v, w} P ν)
    (H : MathFin.levyClosure N.toMathFin) :
    ‖MathFin.itoLevyIntegralL2 N.toMathFin H‖ = ‖H‖ :=
  MathFin.itoLevyIntegralL2_norm N.toMathFin H
end PoissonRandomMeasure

end LevyStochCalc.Poisson


