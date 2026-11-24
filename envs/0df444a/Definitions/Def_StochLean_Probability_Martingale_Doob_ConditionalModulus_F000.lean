-- Prove2me | Definitions.Def_StochLean_Probability_Martingale_Doob_ConditionalModulus_F000
-- name    : StochLean_Probability_Martingale_Doob_ConditionalModulus_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:12.89163+00:00
-- url     : https://prove2.me/theorems/15b01c78-5e46-4770-ae62-3b48ad2bb31b
-- title:
--   StochLean: Probability.Martingale.Doob.ConditionalModulus F000

import Definitions.Def_StochLean_ForMathlib_MeasureTheory_Function_EssentialFamilySupremum_F000
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Version-safe conditional increment moduli

The compact short-window modulus is specified as a measurable essential supremum,
not as the pointwise supremum of arbitrarily chosen uncountably many conditional
expectations. Existence and almost-sure uniqueness precede any representative choice.
The diagonal is included, so taking positive parts does not change a consistent
supremum. These interfaces do not yet assert small-window convergence.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

/-- Ordered pairs on a compact horizon with the specified closed-width bound. -/
abbrev ConditionalIncrementIndex (T δ : ℝ≥0) :=
  {p : ℝ≥0 × ℝ≥0 // p.1 ≤ p.2 ∧ p.2 ≤ T ∧ p.2 ≤ p.1 + δ}
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

noncomputable def conditionalIncrementFamily (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (T δ : ℝ≥0)
    (i : ConditionalIncrementIndex T δ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (P[X i.1.1 - X i.1.2 | F i.1.1] ω)
/-- The conditional modulus is a measurable least almost-sure upper bound.
Individual conditional expectations may have different null exceptional events. -/
abbrev IsConditionalIncrementModulus (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (T δ : ℝ≥0) (W : Ω → ℝ≥0∞) : Prop :=
  IsAEFamilySupremum P (conditionalIncrementFamily F P X T δ) W
variable {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
  {T δ η : ℝ≥0} {W V : Ω → ℝ≥0∞}

end ProbabilityTheory


