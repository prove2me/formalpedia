-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProfile_F000
-- name    : LevyStochCalc_Poisson_CompensatedProfile_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:17:47.970182+00:00
-- url     : https://prove2.me/theorems/42c9c169-4511-4c41-8c05-0d8e60160b0a
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProfile
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProfile. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileCharacter_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral of a deterministic mark profile over a step

The compensated step integrals of simple mark profiles obey the isometry
`‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}`, so an `L²(P)` limit of the compensated step
integrals of simple profiles converging in `L²(ν)` is determined, up to a null set, by the limit
profile alone. That limit is the compensated integral over the step `(a, b]` of a
square-integrable deterministic mark profile `f : E → ℝ` against a Poisson random measure with
intensity `ν`. It agrees with the compensated step integral at a simple profile and carries the
Lévy character

  `E[exp (i u J(f))] = exp ((b − a) ∫ (exp (i u f) − 1 − i u f) dν)`.

## Main definitions

* `LevyStochCalc.Poisson.IsCompensatedProfile` — being a strongly measurable `L²(P)` limit at a
  step of the compensated step integrals of every sequence of simple mark profiles converging to
  a mark profile in `L²(ν)`.
* `LevyStochCalc.Poisson.compensatedProfile` — the compensated integral of a square-integrable
  deterministic mark profile over a step.

## Main statements

* `LevyStochCalc.Poisson.ae_eq_of_tendsto_stepIntegral` — an `L²(P)` limit of the compensated
  step integrals of simple profiles converging in `L²(ν)` depends only on the limit profile.
* `LevyStochCalc.Poisson.stronglyMeasurable_compensatedProfile`,
  `LevyStochCalc.Poisson.memLp_compensatedProfile` — measurability and square integrability.
* `LevyStochCalc.Poisson.tendsto_stepIntegral_compensatedProfile` — the compensated step
  integrals of simple profiles converging to a profile in `L²(ν)` converge to its compensated
  integral in `L²(P)`.
* `LevyStochCalc.Poisson.compensatedProfile_toFun` — agreement with the compensated step
  integral at a simple mark profile.
* `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile` — the Lévy character of the
  compensated integral of a mark profile over a step.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Independence of the approximating sequence -/

/-- The `L²` seminorm of a difference through two intermediate functions. -/
private theorem eLpNorm_sub_le_three {α : Type*} [MeasurableSpace α] {m : Measure α}
    {F H X Y : α → ℝ} (h1 : AEStronglyMeasurable (fun x => X x - F x) m)
    (h2 : AEStronglyMeasurable (fun x => X x - Y x) m)
    (h3 : AEStronglyMeasurable (fun x => Y x - H x) m) :
    eLpNorm (fun x => F x - H x) 2 m
      ≤ eLpNorm (fun x => X x - F x) 2 m + eLpNorm (fun x => X x - Y x) 2 m
        + eLpNorm (fun x => Y x - H x) 2 m := by
  have hsplit : (fun x => F x - H x)
      = -((fun x => X x - F x) - ((fun x => X x - Y x) + fun x => Y x - H x)) := by
    funext x
    simp only [Pi.neg_apply, Pi.sub_apply, Pi.add_apply]
    ring
  rw [hsplit, eLpNorm_neg, add_assoc]
  refine (eLpNorm_sub_le h1 (h2.add h3) one_le_two).trans ?_
  gcongr
  exact eLpNorm_add_le h2 h3 one_le_two
/-! ### The compensated integral of a mark profile over a step -/

/-! ### Agreement at a simple mark profile -/

/-! ### The character -/

end LevyStochCalc.Poisson


