-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterVanish_F000
-- name    : LevyStochCalc_Poisson_CharacterVanish_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:14:24.615276+00:00
-- url     : https://prove2.me/theorems/9c9bae17-5132-41be-a546-41e78b76fda5
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterVanish
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterVanish. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterGronwall_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing with the characters vanishes

For a square-integrable weight of mean zero orthogonal to every compensated integral over the
horizon, the pairing `u(t) = 𝔼[r · χ_t]` with the character of the window counts up to `t` is
bounded by `2 ν(A)` times its own running integral, so the Grönwall iteration makes it vanish on
`[0, T]`. The weight is therefore orthogonal to the character of every finite family of window
sets inside `(0, T] × A`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- With no window at all the characters are constant, so the pairing is the mean of the
weight. -/
theorem charPairing_of_forall_eq_empty (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hB : ∀ j, Bfam j = ∅) (r : Ω → ℝ) (t : ℝ) :
    charPairing N w Bfam r t = ((∫ ω, r ω ∂P : ℝ) : ℂ) := by
  have hchar : ∀ ω, charAt N w Bfam t ω = 1 := fun ω => by simp [charAt, hB]
  rw [charPairing]
  simp_rw [hchar, mul_one]
  exact integral_ofReal
end LevyStochCalc.Poisson


