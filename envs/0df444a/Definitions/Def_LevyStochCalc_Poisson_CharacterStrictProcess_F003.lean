-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F003
-- name    : LevyStochCalc_Poisson_CharacterStrictProcess_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:00:02.388587+00:00
-- url     : https://prove2.me/theorems/39d500c3-1b43-4257-a6ce-8bc8b00a037d
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterStrictProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterStrictProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterCell_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The strict-past character as a progressively measurable process

The predictable representative of the strictly-past window sum, evaluated at a fixed mark of the
window and at the time clamped to the horizon, is a jointly measurable and progressively
measurable process. For a family carried strictly before the horizon it is exactly the exponent
of the strict-past character at every time, so the strict-past character is itself progressively
measurable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Evaluation

end Evaluation

section Clamped

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
  {A : Set E} {b T : ℝ}

variable (hℱ : IsPoissonFiltration N ℱ) (hBm : ∀ j, MeasurableSet (Bfam j))
  (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)

section Parts

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ)

/-- The chain rule's integrand vanishes off the family. -/
theorem charIntegrand_eq_zero_of_notMem (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ) (ω : Ω)
    {s : ℝ} {e : E} (h : ((s, e) : ℝ × E) ∉ ⋃ j, Bfam j) :
    charIntegrand N w Bfam A T ω s e = 0 := by
  classical
  rw [charIntegrand, Set.indicator_of_notMem h]
  simp
/-- For a family carried after `a` the real part of the integrand vanishes at earlier times. -/
theorem charRe_eq_zero_of_le {Bfam : ι → Set (ℝ × E)} {A : Set E} {a b : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) (T : ℝ) (ω : Ω) {s : ℝ} (hs : s ≤ a) (e : E) :
    charRe N w Bfam A T ω s e = 0 := by
  have h : ((s, e) : ℝ × E) ∉ ⋃ j, Bfam j := by
    intro hmem
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
    exact absurd (hBsub j hj).1.1 (not_lt.mpr hs)
  rw [charRe, charIntegrand_eq_zero_of_notMem N w Bfam A T ω h, Complex.zero_re]
/-- The imaginary part vanishes at times before the family. -/
theorem charIm_eq_zero_of_le {Bfam : ι → Set (ℝ × E)} {A : Set E} {a b : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) (T : ℝ) (ω : Ω) {s : ℝ} (hs : s ≤ a) (e : E) :
    charIm N w Bfam A T ω s e = 0 := by
  have h : ((s, e) : ℝ × E) ∉ ⋃ j, Bfam j := by
    intro hmem
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
    exact absurd (hBsub j hj).1.1 (not_lt.mpr hs)
  rw [charIm, charIntegrand_eq_zero_of_notMem N w Bfam A T ω h, Complex.zero_im]
theorem abs_charRe_le (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ) (ω : Ω) (s : ℝ) (e : E) :
    |charRe N w Bfam A T ω s e| ≤ 2 :=
  (Complex.abs_re_le_norm _).trans (_root_.Prove2MeSourceProof.h_099fb631e9952e9258da9935 N w Bfam A T ω s e)
theorem abs_charIm_le (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ) (ω : Ω) (s : ℝ) (e : E) :
    |charIm N w Bfam A T ω s e| ≤ 2 :=
  (Complex.abs_im_le_norm _).trans (_root_.Prove2MeSourceProof.h_099fb631e9952e9258da9935 N w Bfam A T ω s e)
end Parts

end Clamped

end LevyStochCalc.Poisson


