-- Prove2me | Definitions.Def_SourceProof_29aeb1b76d0477f3944256c5
-- name    : SourceProof_29aeb1b76d0477f3944256c5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:58:09.210147+00:00
-- url     : https://prove2.me/theorems/d0c83826-70cd-48c0-9965-0d54302c6dc5
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Poisson.norm_charMark_le
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterFubini_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing with the compensator as a time integral of the pairings with the characters

The chain rule's integrand for the family cut at `t` factors as a deterministic mark times the
predictable exponential. Pairing a weight with the compensator and swapping the two integrals
therefore leaves, at each point of the window, the mark times the pairing of the weight with the
character at that time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Fubini

omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem _root_.Prove2MeSourceProof.h_29aeb1b76d0477f3944256c5 (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (t : ℝ) (q : ℝ × E) :
    ‖charMark w Bfam t q‖ ≤ 2 := by
  rw [LevyStochCalc.Poisson.charMark, norm_mul]
  have h1 : ‖(((⋃ j, LevyStochCalc.Poisson.truncFam Bfam t j).indicator (fun _ => (1 : ℝ)) q : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    by_cases h : q ∈ ⋃ j, LevyStochCalc.Poisson.truncFam Bfam t j
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have h2 : ‖Complex.exp (Complex.I * (LevyStochCalc.Poisson.simpleMark w (LevyStochCalc.Poisson.truncFam Bfam t) q : ℂ)) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_exp_I_mul_ofReal, norm_one]
    norm_num
  calc _ ≤ 1 * 2 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 2 := one_mul 2
end Fubini

end LevyStochCalc.Poisson


