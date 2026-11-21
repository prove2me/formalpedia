-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterCell_F000
-- name    : LevyStochCalc_Poisson_CharacterCell_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:55:19.324303+00:00
-- url     : https://prove2.me/theorems/c2095051-648c-4d92-80ad-9a20d56ffb80
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterCell
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterCell. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterStrict_F000
import Definitions.Def_SourceProof_cd97c574c267ae721fae7a6a

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

/-- The jump weight of the character at a time–mark point: the strict-past character times the
increment of the mark's exponential. -/
noncomputable def charJump (N : PoissonRandomMeasure P ν) (w : ι → ℝ) (Bfam : ι → Set (ℝ × E))
    (ω : Ω) (p : ℝ × E) : ℂ :=
  Complex.exp (Complex.I *
      (windowSumStrict N (⋃ j, Bfam j) (simpleMark w Bfam) p.1 ω : ℂ))
    * (Complex.exp (Complex.I * (simpleMark w Bfam p : ℂ)) - 1)
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem norm_charJump_le (N : PoissonRandomMeasure P ν) (w : ι → ℝ) (Bfam : ι → Set (ℝ × E))
    (ω : Ω) (p : ℝ × E) : ‖charJump N w Bfam ω p‖ ≤ 2 := by
  rw [charJump, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  calc ‖Complex.exp (Complex.I * (simpleMark w Bfam p : ℂ)) - 1‖
      ≤ ‖Complex.exp (Complex.I * (simpleMark w Bfam p : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal, norm_one]; norm_num
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The character of the counts up to `s` is measurable at time `s` for a Poisson filtration. -/
theorem stronglyMeasurable_charAt (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) (s : ℝ) :
    StronglyMeasurable[ℱ s] (charAt N w Bfam s) := by
  have hcount : ∀ j, Measurable[ℱ s] fun ω => N.N ω (Bfam j ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ) :=
    fun j => hℱ.measurable (fun p hp => ⟨hp.2.1.2, Set.mem_univ _⟩)
      ((hBm j).inter (measurableSet_Ioc.prod MeasurableSet.univ))
  refine Measurable.stronglyMeasurable ?_
  unfold charAt
  refine Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp ?_))
  exact Finset.measurable_sum _ fun j _ =>
    (ENNReal.measurable_toReal.comp (hcount j)).const_mul (w j)
/-- **The character as a pure-jump process.** Outside one null set the character of the counts up
to `s` is, at every time, its value at `a` plus the integral of the jump weight over the window
of the times in `(a, s]`. -/
theorem ae_forall_charAt_sub (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, charAt N w Bfam s ω
      = 1 + ∫ p in (⋃ j, Bfam j) ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ,
          charJump N w Bfam ω p ∂(N.N ω) := by
  have hBUm : MeasurableSet (⋃ j, Bfam j) := MeasurableSet.iUnion hBm
  have hBUfin : referenceIntensity ν (⋃ j, Bfam j) ≠ ⊤ :=
    ne_top_of_le_ne_top (referenceIntensity_Ioc_prod_ne_top hAν T)
      (measure_mono (Set.iUnion_subset hBsub))
  filter_upwards [_root_.Prove2MeSourceProof.h_cd97c574c267ae721fae7a6a N hBUm hBUfin (simpleMark w Bfam),
    ae_windowSum_simple N hAν w hBm hBsub] with ω hchain hsum s
  have h1 : charAt N w Bfam s ω
      = Complex.exp (Complex.I * (windowSum N (⋃ j, Bfam j) (simpleMark w Bfam) s ω : ℂ)) := by
    rw [charAt, (hsum s).1]
  rw [h1]
  have h2 := (hchain s).1
  have hint : (∫ p in (⋃ j, Bfam j) ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ,
        charJump N w Bfam ω p ∂(N.N ω))
      = ∫ p in (⋃ j, Bfam j) ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ,
          Complex.exp (Complex.I *
              (windowSumStrict N (⋃ j, Bfam j) (simpleMark w Bfam) p.1 ω : ℂ))
            * (Complex.exp (Complex.I * (simpleMark w Bfam p : ℂ)) - 1) ∂(N.N ω) := rfl
  rw [hint, ← h2]
  ring
/-- **The strict-past character as a pure-jump process.** -/
theorem ae_forall_charStrict_sub (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, charStrict N w Bfam s ω
      = 1 + ∫ p in (⋃ j, Bfam j) ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ,
          charJump N w Bfam ω p ∂(N.N ω) := by
  have hBUm : MeasurableSet (⋃ j, Bfam j) := MeasurableSet.iUnion hBm
  have hBUfin : referenceIntensity ν (⋃ j, Bfam j) ≠ ⊤ :=
    ne_top_of_le_ne_top (referenceIntensity_Ioc_prod_ne_top hAν T)
      (measure_mono (Set.iUnion_subset hBsub))
  filter_upwards [_root_.Prove2MeSourceProof.h_cd97c574c267ae721fae7a6a N hBUm hBUfin (simpleMark w Bfam),
    ae_windowSum_simple N hAν w hBm hBsub] with ω hchain hsum s
  have h1 : charStrict N w Bfam s ω
      = Complex.exp (Complex.I *
          (windowSumStrict N (⋃ j, Bfam j) (simpleMark w Bfam) s ω : ℂ)) := by
    rw [charStrict, (hsum s).2]
  rw [h1]
  have h2 := (hchain s).2
  have hint : (∫ p in (⋃ j, Bfam j) ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ,
        charJump N w Bfam ω p ∂(N.N ω))
      = ∫ p in (⋃ j, Bfam j) ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ,
          Complex.exp (Complex.I *
              (windowSumStrict N (⋃ j, Bfam j) (simpleMark w Bfam) p.1 ω : ℂ))
            * (Complex.exp (Complex.I * (simpleMark w Bfam p : ℂ)) - 1) ∂(N.N ω) := rfl
  rw [hint, ← h2]
  ring
section Predictable

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
  (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
  {T : ℝ} (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A)

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
include hBm hA hAν hBsub in
/-- On the window the jump weight is the predictable integrand of the chain rule. -/
theorem ae_forall_setIntegral_charJump_eq :
    ∀ᵐ ω ∂P, ∀ S : Set ℝ, MeasurableSet S → (∀ x ∈ S, 0 < x) →
      (∫ p in (⋃ j, Bfam j) ∩ S ×ˢ Set.univ, charJump N w Bfam ω p ∂(N.N ω))
        = ∫ q in (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ S ×ˢ Set.univ,
            charIntegrand N w Bfam A T ω q.1 q.2 ∂(N.N ω) := by
  have hBUm : MeasurableSet (⋃ j, Bfam j) := MeasurableSet.iUnion hBm
  have hBsub' : (⋃ j, Bfam j) ⊆ Set.Ioc (0 : ℝ) T ×ˢ A := Set.iUnion_subset hBsub
  filter_upwards [ae_windowSum_simple N hAν w hBm hBsub] with ω hsim S hSm _hSpos
  have hWm : MeasurableSet ((Set.Ioc (0 : ℝ) T ×ˢ A) ∩ S ×ˢ Set.univ) :=
    (measurableSet_Ioc.prod hA).inter (hSm.prod MeasurableSet.univ)
  have hpt : Set.EqOn (fun q : ℝ × E => charIntegrand N w Bfam A T ω q.1 q.2)
      ((⋃ j, Bfam j).indicator (fun p : ℝ × E => charJump N w Bfam ω p))
      ((Set.Ioc (0 : ℝ) T ×ˢ A) ∩ S ×ˢ Set.univ) := by
    intro q hq
    have hq1 : (0 : ℝ) < q.1 := hq.1.1.1
    have hq2 : q.1 ≤ T := hq.1.1.2
    have hq3 : q.2 ∈ A := hq.1.2
    simp only [charIntegrand, charJump]
    rw [predStrict_eq N w Bfam hq1 hq2 hq3 ω, ← (hsim q.1).2]
    by_cases hmem : q ∈ ⋃ j, Bfam j
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      push_cast
      ring
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
      simp
  have hsets : (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ S ×ˢ Set.univ ∩ (⋃ j, Bfam j)
      = (⋃ j, Bfam j) ∩ S ×ˢ Set.univ := by
    refine Set.Subset.antisymm (fun q hq => ⟨hq.2, hq.1.2⟩)
      (fun q hq => ⟨⟨hBsub' hq.1, hq.2⟩, hq.1⟩)
  rw [setIntegral_congr_fun hWm hpt, setIntegral_indicator hBUm, hsets]
include hBm hA hAν hBsub in
/-- **The character as a pure-jump process, with the predictable weight.** -/
theorem ae_forall_charAt_sub_pred :
    ∀ᵐ ω ∂P, ∀ s : ℝ, charAt N w Bfam s ω
      = 1 + ∫ q in (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ,
          charIntegrand N w Bfam A T ω q.1 q.2 ∂(N.N ω) := by
  filter_upwards [ae_forall_charAt_sub N w hBm hAν hBsub,
    ae_forall_setIntegral_charJump_eq N w hBm hA hAν hBsub] with ω h1 h2 s
  rw [h1 s, h2 (Set.Ioc (0 : ℝ) s) measurableSet_Ioc fun x hx => hx.1]
include hBm hA hAν hBsub in
/-- **The strict-past character as a pure-jump process, with the predictable weight.** -/
theorem ae_forall_charStrict_sub_pred :
    ∀ᵐ ω ∂P, ∀ s : ℝ, charStrict N w Bfam s ω
      = 1 + ∫ q in (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ,
          charIntegrand N w Bfam A T ω q.1 q.2 ∂(N.N ω) := by
  filter_upwards [ae_forall_charStrict_sub N w hBm hAν hBsub,
    ae_forall_setIntegral_charJump_eq N w hBm hA hAν hBsub] with ω h1 h2 s
  rw [h1 s, h2 (Set.Ioo (0 : ℝ) s) measurableSet_Ioo fun x hx => hx.1]
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem charAt_zero (ω : Ω) : charAt N w Bfam 0 ω = 1 := by
  have h : ∀ j, Bfam j ∩ Set.Ioc (0 : ℝ) 0 ×ˢ (Set.univ : Set E) = ∅ := by
    intro j
    rw [Set.Ioc_self, Set.empty_prod, Set.inter_empty]
  simp [charAt]
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem charStrict_zero (ω : Ω) : charStrict N w Bfam 0 ω = 1 := by
  have h : ∀ j, Bfam j ∩ Set.Ioo (0 : ℝ) 0 ×ˢ (Set.univ : Set E) = ∅ := by
    intro j
    rw [Set.Ioo_self, Set.empty_prod, Set.inter_empty]
  simp [charStrict]
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem norm_charAt (s : ℝ) (ω : Ω) : ‖charAt N w Bfam s ω‖ = 1 := by
  rw [charAt, Complex.norm_exp_I_mul_ofReal]
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem norm_charStrict (s : ℝ) (ω : Ω) : ‖charStrict N w Bfam s ω‖ = 1 := by
  rw [charStrict, Complex.norm_exp_I_mul_ofReal]
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem abs_charAt_re_le (s : ℝ) (ω : Ω) : |(charAt N w Bfam s ω).re| ≤ 1 := by
  have := Complex.abs_re_le_norm (charAt N w Bfam s ω)
  rwa [norm_charAt N w s ω] at this
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem abs_charAt_im_le (s : ℝ) (ω : Ω) : |(charAt N w Bfam s ω).im| ≤ 1 := by
  have := Complex.abs_im_le_norm (charAt N w Bfam s ω)
  rwa [norm_charAt N w s ω] at this
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem abs_charStrict_re_le (s : ℝ) (ω : Ω) : |(charStrict N w Bfam s ω).re| ≤ 1 := by
  have := Complex.abs_re_le_norm (charStrict N w Bfam s ω)
  rwa [norm_charStrict N w s ω] at this
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem abs_charStrict_im_le (s : ℝ) (ω : Ω) : |(charStrict N w Bfam s ω).im| ≤ 1 := by
  have := Complex.abs_im_le_norm (charStrict N w Bfam s ω)
  rwa [norm_charStrict N w s ω] at this
variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Predictable

end Jump

end LevyStochCalc.Poisson


