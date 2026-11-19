-- Prove2me | Definitions.Def_LevyStochCalc_Probability_Progressive_F002
-- name    : LevyStochCalc_Probability_Progressive_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:25:42.734922+00:00
-- url     : https://prove2.me/theorems/71664b9a-ac21-47ce-9707-c616af5be034
-- title:
--   Source declarations: LevyStochCalc.Probability.Progressive
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.Progressive. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Progressive_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Progressively measurable real processes

`ProgressivelyMeasurable ℱ H` says that the process `H : Ω → ℝ → E`, viewed as a function of
`(ω, s)`, is `ℱ t ⊗ Borel`-measurable on the time window `s ≤ t`, for every `t`. This is
the progressive measurability of Mathlib's `IsStronglyProgressive`, phrased on `Ω × ℝ` by
truncating the time variable at `t`, which is the form in which the stochastic integrals of
this library consume it; `isStronglyProgressive` and `of_isStronglyProgressive` relate the
two.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω}

section General

variable [TopologicalSpace E] [Zero E] [TopologicalSpace F] [Zero F]

namespace ProgressivelyMeasurable

variable {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → E}

end ProgressivelyMeasurable

end General

section Mul

variable [TopologicalSpace E] [MulZeroClass E] [ContinuousMul E] {ℱ : Filtration ℝ mΩ}

end Mul

section Add

variable [NormedAddCommGroup E] {ℱ : Filtration ℝ mΩ}

end Add

section Integral

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → E}

end Integral

section Marked

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace F] [Zero F]

namespace MarkedProgressivelyMeasurable

variable {ℱ : Filtration ℝ mΩ} {φ : Ω → ℝ → E → F}

/-- Restricting the times to a measurable set preserves progressive measurability. -/
theorem indicator_time (h : MarkedProgressivelyMeasurable ℱ φ) {S : Set ℝ}
    (hS : MeasurableSet S) :
    MarkedProgressivelyMeasurable ℱ fun ω s e => S.indicator (fun _ => φ ω s e) s := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hrw : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun s => S.indicator (fun _ => φ p.1 s p.2.2) s) p.2.1)
      = {p : Ω × ℝ × E | p.2.1 ∈ S}.indicator
        (fun p => (Set.Iic t).indicator (fun s => φ p.1 s p.2.2) p.2.1) := by
    funext p
    by_cases ht : p.2.1 ∈ Set.Iic t <;> by_cases hp : p.2.1 ∈ S <;> simp [ht, hp]
  rw [hrw]
  exact (h t).indicator (measurable_snd.fst hS)
end MarkedProgressivelyMeasurable

end Marked

section MarkedIntegral

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ℱ : Filtration ℝ mΩ} {φ : Ω → ℝ → E → F}

end MarkedIntegral

/-! ### Countable suprema of real progressively measurable processes -/

section RealLimsup

variable {ℱ : Filtration ℝ mΩ}

end RealLimsup

end LevyStochCalc.Probability


