-- Prove2me | Definitions.Def_SourceProof_b2f62c96bf5d0e1e1ceca423
-- name    : SourceProof_b2f62c96bf5d0e1e1ceca423
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:56:57.435748+00:00
-- url     : https://prove2.me/theorems/a0b508b9-dd77-455c-9a88-dded0eb594a3
-- title:
--   LevyStochCalc source module: SourceProof_b2f62c96bf5d0e1e1ceca423
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.ae_forall_charStrict_re_im_sub` comes from the `LevyStochCalc.Poisson.CharacterCell` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterCell_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The character of a window family as a pure-jump process

For a finite family of window sets inside `(a, b] × A`, the real and imaginary parts of the
character `charAt` of the counts up to `s` are bounded by one, are measurable at time `s` for a
Poisson filtration, and, outside one null set, satisfy at every time the jump identity
`Y s = Y a + ∫_{(a, s] × A} g dN` whose weight `g` is the corresponding part of
`exp (i · windowSumStrict) (exp (i · mark) − 1)`, bounded by two. This is the shape the product
rule for a continuous Itô process and a pure-jump process asks for.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Jump

section Predictable

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
  (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
  {T : ℝ} (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A)

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

include hBm hA hAν hBsub in

theorem _root_.Prove2MeSourceProof.h_b2f62c96bf5d0e1e1ceca423 (hℱ : IsPoissonFiltration N ℱ) :
    ∀ᵐ ω ∂P, ∀ s : ℝ,
      ((charStrict N w Bfam s ω).re = (charAt N w Bfam 0 ω).re
          + ∫ q in (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ,
              charRe N w Bfam A T ω q.1 q.2 ∂(N.N ω))
        ∧ ((charStrict N w Bfam s ω).im = (charAt N w Bfam 0 ω).im
          + ∫ q in (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ,
              charIm N w Bfam A T ω q.1 q.2 ∂(N.N ω)) := by
  have hWm : MeasurableSet ((Set.Ioc (0 : ℝ) T ×ˢ A : Set (ℝ × E))) :=
    measurableSet_Ioc.prod hA
  have hWfin : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ≠ ⊤ :=
    LevyStochCalc.Poisson.referenceIntensity_Ioc_prod_ne_top hAν T
  filter_upwards [LevyStochCalc.Poisson.ae_forall_charStrict_sub_pred N w hBm hA hAν hBsub,
    N.integer_valued hWm hWfin] with ω hω hnat s
  obtain ⟨n, hn⟩ := hnat
  haveI : IsFiniteMeasure ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) :=
    ⟨by rw [Measure.restrict_apply_univ, hn]; exact ENNReal.natCast_lt_top n⟩
  have hint : IntegrableOn (fun q : ℝ × E => LevyStochCalc.Poisson.charIntegrand N w Bfam A T ω q.1 q.2)
      ((Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ) (N.N ω) :=
    (LevyStochCalc.Poisson.integrableOn_charIntegrand N hℱ w hBm hA hAν hBsub ω).mono_set Set.inter_subset_left
  have hsplit := LevyStochCalc.Poisson.setIntegral_complex_split hint
  rw [LevyStochCalc.Poisson.charAt_zero N w]
  refine ⟨?_, ?_⟩
  · rw [hω s, hsplit]
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    rfl
  · rw [hω s, hsplit]
    simp only [Complex.add_im, Complex.one_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    rfl
end Predictable

end Jump

end LevyStochCalc.Poisson


